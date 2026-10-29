#!/usr/bin/env node
/**
 * Dev.Cop Proxies — Zero-dependency multi-source proxy aggregator & verifier.
 *
 * Pulls already-verified candidates from independent public feeds (never blind
 * port-scanning), schedules candidates fairly across EVERY available country,
 * performs real SOCKS5 / SOCKS4 / HTTP CONNECT + verified TLS 443 handshakes
 * against `api.ipify.org` and `gemini.google.com`, and emits `proxies.json` in
 * the exact schema consumed by Dev.Cop Panel.
 */

import net from "node:net";
import tls from "node:tls";
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

export const UPSTREAM_FEEDS = [
	{ name: "maximilianfeix", url: "https://raw.githubusercontent.com/maximilianfeix/free-proxy-list/main/proxies.json" },
	{ name: "proxyscrape", url: "https://raw.githubusercontent.com/ProxyScrape/free-proxy-list/main/proxies/all/data.json" },
	{ name: "monosans", url: "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies.json" },
	{ name: "xyzs996", url: "https://raw.githubusercontent.com/xyzs996/free-proxy-health-list/main/proxies/stability/stable/data.json" },
	{ name: "litportnet", url: "https://raw.githubusercontent.com/litportnet/free-proxy-list/live/proxies/stable.json" },
	{ name: "vakhov", url: "https://raw.githubusercontent.com/vakhov/fresh-proxy-list/master/proxylist.json" },
];

const FETCH_TIMEOUT_MS = Number(process.env.FETCH_TIMEOUT_MS || 15_000);
const PROBE_TIMEOUT_MS = Number(process.env.PROBE_TIMEOUT_MS || 3_500);
const CONCURRENCY = Number(process.env.CONCURRENCY || 60);
const MAX_CANDIDATES = Number(process.env.MAX_CANDIDATES || 3_600);
const MIN_PER_COUNTRY = Number(process.env.MIN_PER_COUNTRY || 40);

const REGION_NAMES = typeof Intl !== "undefined" && Intl.DisplayNames ? new Intl.DisplayNames(["en"], { type: "region" }) : null;

function isValidPort(port) {
	return Number.isInteger(port) && port > 0 && port <= 65535;
}

function normalizeCountry(value) {
	if (typeof value !== "string" && typeof value !== "number") return null;
	const code = String(value).trim().toUpperCase();
	return /^[A-Z]{2}$/.test(code) ? code : null;
}

function countryNameEn(code, explicitName = null) {
	if (explicitName && String(explicitName).trim().length > 2 && !normalizeCountry(explicitName)) {
		return String(explicitName).trim();
	}
	if (!code) return null;
	try {
		return REGION_NAMES?.of(code) || null;
	} catch {
		return null;
	}
}

function normalizeProtocol(raw, fallback = "socks5") {
	const value = String(raw || fallback).trim().toLowerCase();
	if (value === "https") return "http";
	return ["socks5", "socks4", "http"].includes(value) ? value : fallback;
}

function finiteNonNegative(value) {
	if (value === null || value === undefined || value === "") return null;
	const n = Number(value);
	return Number.isFinite(n) && n >= 0 ? n : null;
}

function parseEndpoint(raw, fallbackProtocol = "socks5") {
	let text = String(raw || "").trim();
	if (!text) return null;
	let protocol = normalizeProtocol(fallbackProtocol);
	const scheme = text.match(/^(socks5|socks4|http|https):\/\//i);
	if (scheme) {
		protocol = normalizeProtocol(scheme[1]);
		text = text.slice(scheme[0].length);
	}
	let username = null;
	let password = null;
	const at = text.lastIndexOf("@");
	if (at > -1) {
		const creds = text.slice(0, at).split(":");
		username = creds[0] || null;
		password = creds.slice(1).join(":") || null;
		text = text.slice(at + 1);
	}
	const colon = text.lastIndexOf(":");
	if (colon < 1) return null;
	const host = text.slice(0, colon).replace(/^\[|\]$/g, "").trim();
	const port = Number(text.slice(colon + 1).trim());
	if (!host || !isValidPort(port)) return null;
	return { protocol, host, port, username, password };
}

/** Normalize one upstream JSON record from any supported feed. */
export function normalizeUpstreamEntry(entry) {
	if (!entry || typeof entry !== "object") return null;

	// vakhov stores protocol booleans ("socks5": "1", "socks4": "1", "http": "1", "ssl": "1")
	let hintedProto = entry.protocol || entry.ptype || null;
	if (!hintedProto) {
		if (entry.socks5 === "1" || entry.socks5 === 1 || entry.socks5 === true) hintedProto = "socks5";
		else if (entry.socks4 === "1" || entry.socks4 === 1 || entry.socks4 === true) hintedProto = "socks4";
		else if (entry.http === "1" || entry.http === 1 || entry.ssl === "1" || entry.ssl === 1) hintedProto = "http";
	}

	let host = String(entry.ip || entry.host || entry.address || "").trim().replace(/^\[|\]$/g, "");
	let port = Number(entry.port);
	let parsed = null;
	if ((!host || !isValidPort(port)) && (entry.url || entry.proxy)) {
		parsed = parseEndpoint(entry.url || entry.proxy, hintedProto || "socks5");
		if (parsed) {
			host = host || parsed.host;
			if (!isValidPort(port)) port = parsed.port;
		}
	}
	if (!host || !isValidPort(port)) return null;
	// Prefer numeric IPv4/IPv6 literal when `entry.ip` is available (avoids stale rDNS hostnames)
	if (entry.ip && net.isIP(String(entry.ip).trim())) host = String(entry.ip).trim();

	const protocol = normalizeProtocol(hintedProto || parsed?.protocol || "socks5");
	const geo = entry.geolocation && typeof entry.geolocation === "object" ? entry.geolocation : {};
	const country =
		normalizeCountry(geo?.country?.iso_code) ||
		normalizeCountry(entry.country_code) ||
		normalizeCountry(entry.country) ||
		normalizeCountry(typeof geo?.country === "string" ? geo.country : null);

	const country_name = countryNameEn(
		country,
		geo?.country?.names?.en || entry.country_name || (typeof entry.country === "string" && entry.country.length > 2 ? entry.country : null)
	);
	const rawCity = geo?.city?.names?.en || (typeof geo?.city === "string" ? geo.city : null) || entry.city || null;
	const city = rawCity && String(rawCity).trim() && String(rawCity).trim().toLowerCase() !== "unknown" ? String(rawCity).trim() : null;

	const timeoutSec = finiteNonNegative(entry.timeout);
	const latencyMs =
		finiteNonNegative(entry.latency_ms) ??
		finiteNonNegative(entry.latencyMs) ??
		finiteNonNegative(entry.latency) ??
		finiteNonNegative(entry.delay);
	const upstreamTimeout = timeoutSec !== null ? timeoutSec : latencyMs !== null ? latencyMs / 1000 : null;

	const https =
		typeof entry.https === "boolean"
			? entry.https
			: typeof entry.ssl === "boolean"
				? entry.ssl
				: typeof entry.supportsHttps === "boolean"
					? entry.supportsHttps
					: entry.ssl === "1" || entry.ssl === 1
						? true
						: null;

	// Skip HTTP proxies explicitly proved unable to tunnel HTTPS
	if (protocol === "http" && https === false) return null;

	const blocklisted =
		entry.blocklisted === true ||
		(typeof entry.threat === "string" && entry.threat.trim() !== "" && entry.threat.trim().toLowerCase() !== "none");
	if (blocklisted) return null;

	const hosting =
		typeof entry.hosting === "boolean"
			? entry.hosting
			: typeof entry.networkType === "string"
				? entry.networkType.toLowerCase() === "hosting"
				: null;

	const uptime =
		finiteNonNegative(entry.uptime) ??
		finiteNonNegative(entry.uptime_24h) ??
		finiteNonNegative(entry.uptime_percent) ??
		finiteNonNegative(entry.reliabilityScore);

	const org =
		entry.asn?.autonomous_system_organization ||
		geo?.asn?.autonomous_system_organization ||
		entry.org ||
		entry.asn_org ||
		entry.asnOrg ||
		entry.isp ||
		null;

	return {
		protocol,
		host,
		port,
		username: entry.username ? String(entry.username) : parsed?.username || null,
		password: entry.password ? String(entry.password) : parsed?.password || null,
		country,
		country_name,
		city,
		org: org ? String(org) : null,
		upstream_timeout: upstreamTimeout,
		upstream_https: https,
		upstream_google: entry.google_ok === true || entry.sites?.google === true,
		hosting,
		anonymity: typeof entry.anonymity === "string" ? entry.anonymity.toLowerCase() : null,
		uptime,
	};
}

function upstreamPriorityScore(c) {
	let score = 0;
	if (c.upstream_google) score -= 1000;
	if (c.upstream_https === true) score -= 300;
	if (c.protocol === "socks5") score -= 120;
	if (c.hosting === false) score -= 150;
	if (c.anonymity === "elite") score -= 40;
	if (c.uptime !== null) score -= Math.min(100, c.uptime);
	score += Math.min(50, (c.upstream_timeout ?? 5) * 10);
	return score;
}

/**
 * Country-fair round-robin selection: guarantees every available country gets
 * representation (up to `minPerCountry` first, then global fill to `maxTotal`).
 */
export function scheduleCountryFairCandidates(candidates, { maxTotal = MAX_CANDIDATES, minPerCountry = MIN_PER_COUNTRY } = {}) {
	const groups = new Map();
	for (const item of candidates) {
		const key = item.country || "ZZ";
		if (!groups.has(key)) groups.set(key, []);
		groups.get(key).push(item);
	}
	for (const list of groups.values()) {
		list.sort((a, b) => upstreamPriorityScore(a) - upstreamPriorityScore(b));
	}

	const selected = [];
	const cursors = new Map([...groups.keys()].map((k) => [k, 0]));

	// Pass 1: round-robin up to minPerCountry so no small country is starved
	for (let round = 0; round < minPerCountry && selected.length < maxTotal; round++) {
		let added = false;
		for (const [key, list] of groups.entries()) {
			if (selected.length >= maxTotal) break;
			if (round < list.length) {
				selected.push(list[round]);
				cursors.set(key, round + 1);
				added = true;
			}
		}
		if (!added) break;
	}

	// Pass 2: fill remaining budget with highest-priority remaining candidates
	if (selected.length < maxTotal) {
		const leftovers = [];
		for (const [key, list] of groups.entries()) {
			const start = cursors.get(key) || 0;
			for (let i = start; i < list.length; i++) leftovers.push(list[i]);
		}
		leftovers.sort((a, b) => upstreamPriorityScore(a) - upstreamPriorityScore(b));
		for (const item of leftovers) {
			if (selected.length >= maxTotal) break;
			selected.push(item);
		}
	}

	return selected;
}

/** Classify HTTP response from `https://gemini.google.com/app`. */
export function classifyGeminiHttp(text) {
	const sep = text.indexOf("\r\n\r\n");
	if (sep < 0) return null;
	const head = text.slice(0, sep);
	const body = text.slice(sep + 4);
	const status = Number(head.match(/^HTTP\/1\.[01] (\d{3})\b/)?.[1] || 0);
	if (!status) return { reachable: false, google_ok: false, gemini_ok: false };

	const location = head.match(/\r\nlocation:\s*([^\r\n]+)/i)?.[1]?.trim() || "";
	if (status === 429 || status === 403 || /\/sorry\/|ipv[46]\.google\.com\/sorry/i.test(location)) {
		return { reachable: true, google_ok: false, gemini_ok: false };
	}
	if (status >= 300 && status < 400) {
		if (/unsupported|\/gemini\/answer\/|faq.*country|regions/i.test(location)) {
			return { reachable: true, google_ok: true, gemini_ok: false };
		}
		if (/google\.com|gemini\.google\.com/i.test(location) || location.startsWith("/")) {
			return { reachable: true, google_ok: true, gemini_ok: true };
		}
		return { reachable: true, google_ok: false, gemini_ok: false };
	}
	if (status === 200) {
		if (/detected unusual traffic|\/sorry\/index/i.test(body)) {
			return { reachable: true, google_ok: false, gemini_ok: false };
		}
		if (/isn['’]t currently supported in your country|not available in your country/i.test(body)) {
			return { reachable: true, google_ok: true, gemini_ok: false };
		}
		if (/gemini|gstatic\.com|<html|<!doctype html/i.test(body)) {
			return { reachable: true, google_ok: true, gemini_ok: true };
		}
		return null;
	}
	return { reachable: true, google_ok: false, gemini_ok: false };
}

/* ── Low-level SOCKS5 / SOCKS4a / HTTP CONNECT dialers over node:net ────── */

function readBytes(socket, minBytes, deadlineMs, stash) {
	return new Promise((resolve, reject) => {
		if (stash.buf.length >= minBytes) {
			const out = stash.buf.subarray(0, minBytes);
			stash.buf = stash.buf.subarray(minBytes);
			return resolve(out);
		}
		const remain = deadlineMs - Date.now();
		if (remain <= 0) return reject(new Error("handshake timeout"));
		const timer = setTimeout(() => {
			cleanup();
			reject(new Error("handshake timeout"));
		}, remain);
		function onData(chunk) {
			stash.buf = Buffer.concat([stash.buf, chunk]);
			if (stash.buf.length >= minBytes) {
				cleanup();
				const out = stash.buf.subarray(0, minBytes);
				stash.buf = stash.buf.subarray(minBytes);
				resolve(out);
			}
		}
		function onClose() {
			cleanup();
			reject(new Error("closed during handshake"));
		}
		function onError(err) {
			cleanup();
			reject(err);
		}
		function cleanup() {
			clearTimeout(timer);
			socket.off("data", onData);
			socket.off("close", onClose);
			socket.off("end", onClose);
			socket.off("error", onError);
		}
		socket.on("data", onData);
		socket.once("close", onClose);
		socket.once("end", onClose);
		socket.once("error", onError);
	});
}

async function openProxyTunnel(proxy, targetHost, targetPort, timeoutMs) {
	const deadline = Date.now() + timeoutMs;
	const socket = net.connect({ host: proxy.host, port: proxy.port });
	socket.setNoDelay(true);

	await new Promise((resolve, reject) => {
		const timer = setTimeout(() => {
			socket.destroy();
			reject(new Error("connect timeout"));
		}, Math.max(200, deadline - Date.now()));
		socket.once("connect", () => {
			clearTimeout(timer);
			resolve();
		});
		socket.once("error", (err) => {
			clearTimeout(timer);
			reject(err);
		});
	});

	const stash = { buf: Buffer.alloc(0) };
	try {
		if (proxy.protocol === "socks5") {
			const hasAuth = Boolean(proxy.username);
			socket.write(hasAuth ? Buffer.from([0x05, 0x02, 0x00, 0x02]) : Buffer.from([0x05, 0x01, 0x00]));
			const greet = await readBytes(socket, 2, deadline, stash);
			if (greet[0] !== 0x05) throw new Error("not socks5");
			if (greet[1] === 0x02) {
				if (!hasAuth) throw new Error("unexpected auth");
				const u = Buffer.from(proxy.username);
				const p = Buffer.from(proxy.password || "");
				socket.write(Buffer.concat([Buffer.from([0x01, u.length]), u, Buffer.from([p.length]), p]));
				const authReply = await readBytes(socket, 2, deadline, stash);
				if (authReply[1] !== 0x00) throw new Error("socks5 auth failed");
			} else if (greet[1] !== 0x00) {
				throw new Error("socks5 auth rejected");
			}
			const domain = Buffer.from(targetHost);
			const req = Buffer.alloc(4 + 1 + domain.length + 2);
			req[0] = 0x05;
			req[1] = 0x01;
			req[2] = 0x00;
			req[3] = 0x03;
			req[4] = domain.length;
			domain.copy(req, 5);
			req.writeUInt16BE(targetPort, 5 + domain.length);
			socket.write(req);
			const head = await readBytes(socket, 4, deadline, stash);
			if (head[0] !== 0x05 || head[1] !== 0x00) throw new Error(`socks5 code ${head[1]}`);
			if (head[3] === 0x01) await readBytes(socket, 6, deadline, stash);
			else if (head[3] === 0x04) await readBytes(socket, 18, deadline, stash);
			else if (head[3] === 0x03) {
				const len = (await readBytes(socket, 1, deadline, stash))[0];
				await readBytes(socket, len + 2, deadline, stash);
			} else throw new Error("bad socks5 atyp");
		} else if (proxy.protocol === "socks4") {
			const user = Buffer.from(proxy.username || "anonymous");
			const domain = Buffer.from(targetHost);
			const req = Buffer.alloc(8 + user.length + 1 + domain.length + 1);
			req[0] = 0x04;
			req[1] = 0x01;
			req.writeUInt16BE(targetPort, 2);
			req[4] = 0;
			req[5] = 0;
			req[6] = 0;
			req[7] = 1; // SOCKS4a domain extension
			user.copy(req, 8);
			req[8 + user.length] = 0;
			domain.copy(req, 9 + user.length);
			req[9 + user.length + domain.length] = 0;
			socket.write(req);
			const reply = await readBytes(socket, 8, deadline, stash);
			if (reply[1] !== 0x5a) throw new Error("socks4 rejected");
		} else {
			let connectReq = `CONNECT ${targetHost}:${targetPort} HTTP/1.1\r\nHost: ${targetHost}:${targetPort}\r\n`;
			if (proxy.username) {
				const token = Buffer.from(`${proxy.username}:${proxy.password || ""}`).toString("base64");
				connectReq += `Proxy-Authorization: Basic ${token}\r\n`;
			}
			connectReq += "Proxy-Connection: keep-alive\r\n\r\n";
			socket.write(connectReq);

			while (stash.buf.indexOf("\r\n\r\n") === -1) {
				const more = await readBytes(socket, 1, deadline, stash);
				stash.buf = Buffer.concat([more, stash.buf]);
				if (stash.buf.indexOf("\r\n\r\n") !== -1) break;
				// Wait for next chunk cleanly
				await new Promise((resolve, reject) => {
					const rem = deadline - Date.now();
					if (rem <= 0) return reject(new Error("connect header timeout"));
					const t = setTimeout(() => { off(); reject(new Error("connect header timeout")); }, rem);
					const onD = (c) => { off(); stash.buf = Buffer.concat([stash.buf, c]); resolve(); };
					const onE = (e) => { off(); reject(e || new Error("closed")); };
					const off = () => { clearTimeout(t); socket.off("data", onD); socket.off("error", onE); socket.off("close", onE); socket.off("end", onE); };
					socket.once("data", onD);
					socket.once("error", onE);
					socket.once("close", onE);
					socket.once("end", onE);
				});
				if (stash.buf.length > 32768) throw new Error("connect header too large");
			}
			const endIdx = stash.buf.indexOf("\r\n\r\n");
			const headerStr = stash.buf.subarray(0, endIdx).toString("latin1");
			stash.buf = stash.buf.subarray(endIdx + 4);
			const status = Number(headerStr.split("\r\n")[0].match(/HTTP\/1\.[01] (\d{3})/)?.[1] || 0);
			if (status !== 200) throw new Error(`HTTP CONNECT ${status}`);
		}
		if (stash.buf.length > 0) throw new Error("unexpected bytes before TLS");
		return socket;
	} catch (err) {
		socket.destroy();
		throw err;
	}
}

async function httpsGetViaProxy(proxy, { host, path: reqPath, headers = {}, timeoutMs = PROBE_TIMEOUT_MS, earlyClassifier = null, tlsOptions = {} } = {}) {
	const started = Date.now();
	const rawSocket = await openProxyTunnel(proxy, host, 443, timeoutMs);
	const remain = Math.max(400, timeoutMs - (Date.now() - started));

	return await new Promise((resolve, reject) => {
		let settled = false;
		const tlsSocket = tls.connect({
			socket: rawSocket,
			servername: host,
			rejectUnauthorized: true,
			...tlsOptions,
		});
		const timer = setTimeout(() => finish(new Error("tls timeout")), remain);
		let text = "";
		let bytes = 0;

		function finish(err, value) {
			if (settled) return;
			settled = true;
			clearTimeout(timer);
			try { tlsSocket.destroy(); } catch {}
			try { rawSocket.destroy(); } catch {}
			if (err) reject(err);
			else resolve(value);
		}

		tlsSocket.once("secureConnect", () => {
			const hdrLines = Object.entries({
				Host: host,
				"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
				Connection: "close",
				"Accept-Encoding": "identity",
				...headers,
			}).map(([k, v]) => `${k}: ${v}`).join("\r\n");
			tlsSocket.write(`GET ${reqPath} HTTP/1.1\r\n${hdrLines}\r\n\r\n`);
		});

		tlsSocket.on("data", (chunk) => {
			bytes += chunk.length;
			text += chunk.toString("utf8");
			if (earlyClassifier) {
				const verdict = earlyClassifier(text);
				if (verdict) return finish(null, { text, verdict, latencyMs: Date.now() - started });
			}
			if (bytes > 24 * 1024) finish(null, { text, verdict: earlyClassifier ? earlyClassifier(text) : null, latencyMs: Date.now() - started });
		});
		tlsSocket.once("end", () => finish(null, { text, verdict: earlyClassifier ? earlyClassifier(text) : null, latencyMs: Date.now() - started }));
		tlsSocket.once("close", () => finish(null, { text, verdict: earlyClassifier ? earlyClassifier(text) : null, latencyMs: Date.now() - started }));
		tlsSocket.once("error", (err) => finish(err));
	});
}

/** Verify a single candidate on real TLS 443 (`api.ipify.org` + `gemini.google.com`). */
export async function verifyCandidate(candidate, { timeoutMs = PROBE_TIMEOUT_MS, tlsOptions = {}, targets = {} } = {}) {
	const ipifyHost = targets.ipifyHost || "api.ipify.org";
	const geminiHost = targets.geminiHost || "gemini.google.com";

	const [ipifyRes, geminiRes] = await Promise.allSettled([
		httpsGetViaProxy(candidate, {
			host: ipifyHost,
			path: "/?format=json",
			headers: { "User-Agent": "DevCopProxies/1.0", Accept: "application/json" },
			timeoutMs,
			tlsOptions,
			earlyClassifier: (txt) => {
				const sep = txt.indexOf("\r\n\r\n");
				return sep >= 0 && txt.slice(sep + 4).includes("}") ? true : null;
			},
		}),
		httpsGetViaProxy(candidate, {
			host: geminiHost,
			path: "/app",
			headers: { Accept: "text/html,application/xhtml+xml", "Accept-Language": "en-US,en;q=0.9" },
			timeoutMs,
			tlsOptions,
			earlyClassifier: classifyGeminiHttp,
		}),
	]);

	let exitIp = null;
	let latencyMs = null;
	if (ipifyRes.status === "fulfilled") {
		const txt = ipifyRes.value.text || "";
		if (/^HTTP\/1\.[01] 200\b/.test(txt)) {
			const idx = txt.indexOf("{", txt.indexOf("\r\n\r\n"));
			if (idx !== -1) {
				try { exitIp = JSON.parse(txt.slice(idx))?.ip || null; } catch {}
			}
			if (exitIp) latencyMs = ipifyRes.value.latencyMs;
		}
	}

	let geminiVerdict = { reachable: false, google_ok: false, gemini_ok: false };
	if (geminiRes.status === "fulfilled") {
		geminiVerdict = geminiRes.value.verdict || classifyGeminiHttp(geminiRes.value.text || "") || (
			/^HTTP\/1\.[01] 200\b/.test(geminiRes.value.text || "")
				? { reachable: true, google_ok: true, gemini_ok: true }
				: geminiVerdict
		);
		if (latencyMs === null && geminiVerdict.reachable) latencyMs = geminiRes.value.latencyMs;
	}

	if (!exitIp && !geminiVerdict.reachable) return null;

	let exitCountry = candidate.country;
	let exitCountryName = candidate.country_name;
	if (exitIp && exitIp !== candidate.host && targets.geoLookup !== false) {
		try {
			const ctrl = new AbortController();
			const gt = setTimeout(() => ctrl.abort(), 2_500);
			try {
				const gr = await fetch(`https://get.geojs.io/v1/ip/geo/${encodeURIComponent(exitIp)}.json`, { signal: ctrl.signal });
				if (gr.ok) {
					const gd = await gr.json();
					const cc = normalizeCountry(gd?.country_code);
					if (cc) {
						exitCountry = cc;
						exitCountryName = countryNameEn(cc, gd?.country);
					}
				}
			} finally {
				clearTimeout(gt);
			}
		} catch {}
	}

	return {
		protocol: candidate.protocol,
		username: candidate.username || null,
		password: candidate.password || null,
		host: candidate.host,
		port: candidate.port,
		timeout: Number(((latencyMs ?? timeoutMs) / 1000).toFixed(3)),
		exit_ip: exitIp || candidate.host,
		https: true,
		google_ok: geminiVerdict.google_ok === true,
		gemini_ok: geminiVerdict.gemini_ok === true,
		blocklisted: false,
		hosting: candidate.hosting,
		anonymity: candidate.anonymity,
		uptime: candidate.uptime,
		asn: candidate.org ? { autonomous_system_organization: candidate.org } : undefined,
		geolocation: {
			country: exitCountry
				? {
						iso_code: exitCountry,
						...(exitCountryName ? { names: { en: exitCountryName } } : {}),
					}
				: undefined,
			...(exitCountry === candidate.country && candidate.city ? { city: { names: { en: candidate.city } } } : {}),
		},
	};
}

export function sortVerifiedProxies(list) {
	return [...list].sort((a, b) => {
		const aTier = a.gemini_ok ? 0 : a.google_ok ? 1 : 2;
		const bTier = b.gemini_ok ? 0 : b.google_ok ? 1 : 2;
		if (aTier !== bTier) return aTier - bTier;
		const aDirect = !a.exit_ip || a.exit_ip === a.host ? 0 : 1;
		const bDirect = !b.exit_ip || b.exit_ip === b.host ? 0 : 1;
		if (aDirect !== bDirect) return aDirect - bDirect;
		return (a.timeout ?? 999) - (b.timeout ?? 999);
	});
}

async function fetchFeed(feed) {
	const controller = new AbortController();
	const timer = setTimeout(() => controller.abort(), FETCH_TIMEOUT_MS);
	try {
		const res = await fetch(feed.url, {
			signal: controller.signal,
			headers: { "User-Agent": "DevCop-Proxy-Aggregator/1.0" },
		});
		if (!res.ok) throw new Error(`HTTP ${res.status}`);
		const data = await res.json();
		const rows = Array.isArray(data) ? data : Array.isArray(data?.proxies) ? data.proxies : [];
		return { name: feed.name, rows };
	} finally {
		clearTimeout(timer);
	}
}

export async function runCollection({ outDir = process.cwd(), feeds = UPSTREAM_FEEDS } = {}) {
	const startedAt = new Date();
	console.log(`[collect] Fetching ${feeds.length} upstream feeds...`);

	const settled = await Promise.allSettled(feeds.map(fetchFeed));
	const byKey = new Map();
	const feedSummary = [];

	for (let i = 0; i < settled.length; i++) {
		const res = settled[i];
		const feedName = feeds[i].name;
		if (res.status !== "fulfilled") {
			console.warn(`[collect] Feed ${feedName} failed: ${res.reason?.message || res.reason}`);
			feedSummary.push({ name: feedName, ok: false, count: 0 });
			continue;
		}
		let accepted = 0;
		for (const raw of res.value.rows) {
			const entry = normalizeUpstreamEntry(raw);
			if (!entry) continue;
			accepted++;
			const key = `${entry.protocol}://${entry.host}:${entry.port}`;
			const existing = byKey.get(key);
			if (!existing) {
				byKey.set(key, entry);
			} else {
				existing.upstream_google = existing.upstream_google || entry.upstream_google;
				if (existing.upstream_https === null && entry.upstream_https !== null) existing.upstream_https = entry.upstream_https;
				if (!existing.country && entry.country) existing.country = entry.country;
				if (!existing.country_name && entry.country_name) existing.country_name = entry.country_name;
				if (!existing.city && entry.city) existing.city = entry.city;
				if (!existing.org && entry.org) existing.org = entry.org;
				if (existing.hosting === null && entry.hosting !== null) existing.hosting = entry.hosting;
				if (existing.uptime === null && entry.uptime !== null) existing.uptime = entry.uptime;
			}
		}
		console.log(`[collect] Feed ${feedName}: ${accepted} valid candidates`);
		feedSummary.push({ name: feedName, ok: true, count: accepted });
	}

	const uniqueCandidates = [...byKey.values()];
	const scheduled = scheduleCountryFairCandidates(uniqueCandidates);
	const inputCountries = new Set(scheduled.map((c) => c.country).filter(Boolean)).size;
	console.log(`[collect] Deduplicated: ${uniqueCandidates.length} → Scheduled ${scheduled.length} across ${inputCountries} countries (concurrency=${CONCURRENCY})`);

	const verified = [];
	let cursor = 0;
	async function worker() {
		while (cursor < scheduled.length) {
			const idx = cursor++;
			const candidate = scheduled[idx];
			try {
				const result = await verifyCandidate(candidate);
				if (result) verified.push(result);
			} catch {
				/* dead proxy — skip */
			}
		}
	}
	await Promise.all(Array.from({ length: Math.min(CONCURRENCY, Math.max(1, scheduled.length)) }, () => worker()));

	const sorted = sortVerifiedProxies(verified);
	if (sorted.length === 0) {
		throw new Error("Zero working HTTPS proxies verified — aborting publish to preserve last healthy snapshot.");
	}

	const countries = {};
	for (const p of sorted) {
		const cc = p.geolocation?.country?.iso_code || "UNK";
		countries[cc] = (countries[cc] || 0) + 1;
	}

	const stats = {
		updated_at: new Date().toISOString(),
		duration_sec: Number(((Date.now() - startedAt.getTime()) / 1000).toFixed(1)),
		candidates_total: uniqueCandidates.length,
		candidates_tested: scheduled.length,
		working_https: sorted.length,
		google_ok: sorted.filter((p) => p.google_ok).length,
		gemini_ok: sorted.filter((p) => p.gemini_ok).length,
		countries_count: Object.keys(countries).filter((c) => c !== "UNK").length,
		protocols: {
			socks5: sorted.filter((p) => p.protocol === "socks5").length,
			socks4: sorted.filter((p) => p.protocol === "socks4").length,
			http: sorted.filter((p) => p.protocol === "http").length,
		},
		countries,
		feeds: feedSummary,
	};

	await fs.mkdir(outDir, { recursive: true });
	await fs.writeFile(path.join(outDir, "proxies.json"), JSON.stringify(sorted));
	await fs.writeFile(path.join(outDir, "stats.json"), JSON.stringify(stats, null, 2) + "\n");

	console.log(
		`[collect] Done in ${stats.duration_sec}s: ${stats.working_https} HTTPS · ${stats.google_ok} Google · ${stats.gemini_ok} Gemini across ${stats.countries_count} countries.`
	);
	return { proxies: sorted, stats };
}

const isMain = process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url));
if (isMain) {
	const outArg = process.argv[2] ? path.resolve(process.argv[2]) : path.resolve(process.cwd(), "out");
	runCollection({ outDir: outArg }).catch((err) => {
		console.error("[collect] Fatal:", err?.message || err);
		process.exit(1);
	});
}
