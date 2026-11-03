#!/usr/bin/env node
/**
 * Dev.Cop Proxies — Zero-dependency multi-source proxy aggregator & verifier.
 *
 * Pulls live-checked candidates from independent public feeds (never blind
 * port-scanning), strips multi-port rotating backconnect farms (e.g. 45.74.31.*),
 * schedules candidates fairly across EVERY country while guaranteeing full
 * coverage for high-demand locations (DE, FR, NL, GB, US, TR, CA, etc.),
 * performs real SOCKS5 / SOCKS4a / HTTP CONNECT + verified TLS 443 handshakes
 * against HTTPS IP-echo services and `gemini.google.com/app`, verifies 2-probe
 * exit-IP stability on NAT/relay servers so country-hopping rotators are
 * rejected without disrupting fixed-exit Gemini proxies, and emits `proxies.json`.
 */

import net from "node:net";
import tls from "node:tls";
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

export const CARRY_FORWARD_URL =
	"https://raw.githubusercontent.com/RezaFKH/devcop-proxies/data/proxies.json";

export const UPSTREAM_FEEDS = [
	{ name: "maximilianfeix", url: "https://raw.githubusercontent.com/maximilianfeix/free-proxy-list/main/proxies.json" },
	{ name: "proxifly", url: "https://raw.githubusercontent.com/proxifly/free-proxy-list/main/proxies/all/data.json" },
	{ name: "hproxy", url: "https://raw.githubusercontent.com/hproxy-com/free-proxy-list/main/live.json" },
	{ name: "proxio", url: "https://raw.githubusercontent.com/proxio-io/proxy-list/main/all.json" },
	{ name: "xyzs996", url: "https://raw.githubusercontent.com/xyzs996/free-proxy-health-list/main/proxies/all/data.json" },
	{ name: "litportnet", url: "https://raw.githubusercontent.com/litportnet/free-proxy-list/live/proxies/all.json" },
	{ name: "monosans", url: "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies.json" },
	{ name: "proxyscrape", url: "https://raw.githubusercontent.com/ProxyScrape/free-proxy-list/main/proxies/all/data.json" },
	{ name: "thordata_socks5", url: "https://raw.githubusercontent.com/Thordata/awesome-free-proxy-list/main/docs/data/socks5.json" },
	{ name: "thordata_https", url: "https://raw.githubusercontent.com/Thordata/awesome-free-proxy-list/main/docs/data/https.json", defaultHttps: true },
	{ name: "thordata_socks4", url: "https://raw.githubusercontent.com/Thordata/awesome-free-proxy-list/main/docs/data/socks4.json" },
	{ name: "vakhov", url: "https://raw.githubusercontent.com/vakhov/fresh-proxy-list/master/proxylist.json" },
];

export const PRIORITY_COUNTRIES = [
	"DE", "FR", "NL", "GB", "CH", "SE", "FI", "NO", "DK", "AT", "BE", "IE",
	"IT", "ES", "PT", "PL", "CZ", "RO", "TR", "CA", "AE", "JP", "KR", "SG", "AU", "US",
];

const IP_ECHO_TARGETS = [
	{ host: "api.ipify.org", path: "/?format=json", accept: "application/json" },
	{ host: "checkip.amazonaws.com", path: "/", accept: "text/plain" },
	{ host: "icanhazip.com", path: "/", accept: "text/plain" },
];

const FETCH_TIMEOUT_MS = Number(process.env.FETCH_TIMEOUT_MS || 22_000);
const CONNECT_TIMEOUT_MS = Number(process.env.CONNECT_TIMEOUT_MS || 2_400);
const PROBE_TIMEOUT_MS = Number(process.env.PROBE_TIMEOUT_MS || 3_500);
const GEMINI_TIMEOUT_MS = Number(process.env.GEMINI_TIMEOUT_MS || 5_200);
const MAX_WALL_TIME_MS = Number(process.env.MAX_WALL_TIME_MS || 390_000);
const CONCURRENCY = Number(process.env.CONCURRENCY || 115);
const MAX_CANDIDATES = Number(process.env.MAX_CANDIDATES || 9_500);
const MIN_PER_COUNTRY = Number(process.env.MIN_PER_COUNTRY || 40);
const PRIORITY_MAX_PER_COUNTRY = Number(process.env.PRIORITY_MAX_PER_COUNTRY || 600);
const MAX_PORTS_PER_HOST_FARM = Number(process.env.MAX_PORTS_PER_HOST_FARM || 4);
const KEEP_PORTS_PER_HOST = Number(process.env.KEEP_PORTS_PER_HOST || 2);
const MAX_VERIFIED_PER_HOST = Number(process.env.MAX_VERIFIED_PER_HOST || 2);
const MAX_VERIFIED_PER_EXIT_IP = Number(process.env.MAX_VERIFIED_PER_EXIT_IP || 2);

const REGION_NAMES = typeof Intl !== "undefined" && Intl.DisplayNames ? new Intl.DisplayNames(["en"], { type: "region" }) : null;

const NON_THREAT_VALUES = new Set(["", "none", "unknown", "clean", "null", "false", "low", "ok"]);
const EXCLUDED_COUNTRIES = new Set(["IR"]);
const EXCLUDED_RELAY_ENTRY_COUNTRIES = new Set(["IR", "CN"]);
const TOR_SOCKS_PORTS = new Set([9050, 9051, 9150, 9151]);

const CF_IPV4_CIDRS = [
	[0x6715f400, 22], [0x6716c800, 22], [0x671f0400, 22], [0x68100000, 12],
	[0x6ca2c000, 18], [0x83004800, 22], [0x8d654000, 18],
	[0xa29e0000, 15], [0xac400000, 13], [0xadf53000, 20], [0xbc726000, 20],
	[0xbe5df000, 20], [0xc6298000, 17],
];

let echoCursor = 0;
const geoCache = new Map();

function isValidPort(port) {
	return Number.isInteger(port) && port > 0 && port <= 65535;
}

function ipv4ToUint32(ip) {
	const parts = String(ip).split(".");
	if (parts.length !== 4) return null;
	let out = 0;
	for (const part of parts) {
		if (!/^\d{1,3}$/.test(part)) return null;
		const n = Number(part);
		if (n < 0 || n > 255) return null;
		out = ((out << 8) | n) >>> 0;
	}
	return out;
}

/** Reject Cloudflare Anycast CDN edge IPs advertised on 80/443 (never forward proxies). */
export function isCloudflareEdgeIp(host) {
	const ipNum = ipv4ToUint32(host);
	if (ipNum === null) return false;
	for (const [base, bits] of CF_IPV4_CIDRS) {
		const mask = bits === 0 ? 0 : (~((1 << (32 - bits)) - 1)) >>> 0;
		if (((ipNum & mask) >>> 0) === ((base & mask) >>> 0)) return true;
	}
	return false;
}

function normalizeCountry(value) {
	if (typeof value !== "string" && typeof value !== "number") return null;
	const code = String(value).trim().toUpperCase();
	return /^[A-Z]{2}$/.test(code) && code !== "ZZ" && code !== "XX" ? code : null;
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
export function normalizeUpstreamEntry(entry, options = {}) {
	if (!entry || typeof entry !== "object") return null;
	const { defaultHttps = null, carryForward = false } = options || {};

	// hproxy & proxio store `protocols: ["socks5", "https", ...]`
	let protoArrayHttps = null;
	let hintedProto = entry.protocol || entry.ptype || entry.type || null;
	if (!hintedProto && Array.isArray(entry.protocols) && entry.protocols.length > 0) {
		const lower = entry.protocols.map((p) => String(p || "").trim().toLowerCase());
		if (lower.includes("socks5")) hintedProto = "socks5";
		else if (lower.includes("socks4")) hintedProto = "socks4";
		else if (lower.includes("https")) {
			hintedProto = "http";
			protoArrayHttps = true;
		} else if (lower.includes("http")) {
			hintedProto = "http";
			protoArrayHttps = false;
		} else {
			// Skip non-443 tunnel types such as `["CONNECT80"]` or `["CONNECT25"]`
			return null;
		}
	}

	// vakhov stores protocol booleans ("socks5": "1", "socks4": "1", "http": "1", "ssl": "1")
	let vakhovHttps = null;
	if (!hintedProto) {
		if (entry.socks5 === "1" || entry.socks5 === 1 || entry.socks5 === true) hintedProto = "socks5";
		else if (entry.socks4 === "1" || entry.socks4 === 1 || entry.socks4 === true) hintedProto = "socks4";
		else if (entry.ssl === "1" || entry.ssl === 1) {
			hintedProto = "http";
			vakhovHttps = true;
		} else if (entry.http === "1" || entry.http === 1) {
			hintedProto = "http";
			if (entry.ssl === "0" || entry.ssl === 0) vakhovHttps = false;
		}
	}

	const rawProtoLower = String(entry.protocol || entry.ptype || entry.type || "").trim().toLowerCase();
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

	// Reject Cloudflare CDN Anycast IPs (reverse proxies, never forward tunnels) and Tor SOCKS daemons
	if (isCloudflareEdgeIp(host)) return null;
	if (TOR_SOCKS_PORTS.has(port)) return null;

	const protocol = normalizeProtocol(hintedProto || parsed?.protocol || "socks5");
	const geo = entry.geolocation && typeof entry.geolocation === "object" ? entry.geolocation : {};
	const country =
		normalizeCountry(geo?.country?.iso_code) ||
		normalizeCountry(entry.country_code) ||
		normalizeCountry(entry.code) ||
		normalizeCountry(entry.country) ||
		normalizeCountry(typeof geo?.country === "string" ? geo.country : null);
	if (country && EXCLUDED_COUNTRIES.has(country)) return null;

	const country_name = countryNameEn(
		country,
		geo?.country?.names?.en || entry.country_name || (typeof entry.country === "string" && entry.country.length > 2 ? entry.country : null)
	);
	const rawCity =
		geo?.city?.names?.en ||
		(typeof geo?.city === "string" ? geo.city : null) ||
		entry.city ||
		entry.location ||
		null;
	const city = rawCity && String(rawCity).trim() && String(rawCity).trim().toLowerCase() !== "unknown" ? String(rawCity).trim() : null;

	const timeoutSec = finiteNonNegative(entry.timeout) ?? finiteNonNegative(entry.latency_s);
	const latencyMs =
		finiteNonNegative(entry.latency_ms) ??
		finiteNonNegative(entry.latencyMs) ??
		finiteNonNegative(entry.latency) ??
		finiteNonNegative(entry.delay) ??
		finiteNonNegative(entry.speed_ms);
	const upstreamTimeout = timeoutSec !== null ? timeoutSec : latencyMs !== null ? latencyMs / 1000 : null;

	const rawHttps =
		rawProtoLower === "https"
			? true
			: protoArrayHttps !== null
				? protoArrayHttps
				: vakhovHttps !== null
					? vakhovHttps
					: typeof entry.https === "boolean"
						? entry.https
						: typeof entry.ssl === "boolean"
							? entry.ssl
							: typeof entry.supportsHttps === "boolean"
								? entry.supportsHttps
								: entry.ssl === "1" || entry.ssl === 1
									? true
									: null;
	const https = rawHttps !== null ? rawHttps : typeof defaultHttps === "boolean" ? defaultHttps : null;

	// Skip HTTP proxies explicitly proved unable to tunnel HTTPS
	if (protocol === "http" && https === false) return null;

	const ipTypeLower = typeof entry.ip_type === "string" ? entry.ip_type.toLowerCase() : "";
	const hosting =
		typeof entry.hosting === "boolean"
			? entry.hosting
			: typeof entry.networkType === "string"
				? entry.networkType.toLowerCase() === "hosting"
				: ipTypeLower === "datacenter" || ipTypeLower === "hosting"
					? true
					: ipTypeLower === "residential" || ipTypeLower === "isp"
						? false
						: null;

	const uptime =
		finiteNonNegative(entry.reliability) ??
		finiteNonNegative(entry.uptime) ??
		finiteNonNegative(entry.uptime_24h) ??
		finiteNonNegative(entry.uptime_percent) ??
		finiteNonNegative(entry.reliabilityScore);

	// `xyzs996` uses `threat: "unknown"` on clean proxies; `maximilianfeix` sets
	// `blocklisted: true` on datacenter ASNs (Hetzner DE, OVH FR, Google Cloud) even
	// when `sites.google === true` or `uptime_24h >= 60`. Keep explicit abuse
	// blocklists dropped while allowing Google-verified/high-uptime cloud hosts.
	const threatStr = typeof entry.threat === "string" ? entry.threat.trim().toLowerCase() : "";
	const hasRealThreat = threatStr !== "" && !NON_THREAT_VALUES.has(threatStr);
	const hasGoogle =
		entry.google_ok === true ||
		entry.google === true ||
		entry.gemini_ok === true ||
		entry.sites?.google === true;
	const trustedCloudHost = hosting === true && (hasGoogle || (uptime !== null && uptime >= 60));
	const blocklisted = hasRealThreat || (entry.blocklisted === true && !trustedCloudHost);
	if (blocklisted) return null;

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
		upstream_google: hasGoogle,
		upstream_gemini: entry.gemini_ok === true,
		carried_forward: Boolean(carryForward),
		hosting,
		anonymity: typeof entry.anonymity === "string" ? entry.anonymity.toLowerCase() : null,
		uptime,
	};
}

function upstreamPriorityScore(c) {
	let score = 0;
	if (c.carried_forward) score -= 1800;
	if (c.upstream_gemini) score -= 1200;
	if (c.upstream_google) score -= 1000;
	if (c.upstream_https === true) score -= 300;
	if (c.protocol === "socks5") score -= 140;
	if (c.hosting === false) score -= 120;
	if (c.anonymity === "elite") score -= 40;
	if (c.uptime !== null) score -= Math.min(100, c.uptime);
	score += Math.min(50, (c.upstream_timeout ?? 5) * 10);
	return score;
}

/**
 * Strip port-multiplexed rotating backconnect farms (such as `45.74.31.40..47`
 * advertising hundreds of ports on one IP whose exit country changes every
 * minute) and cap normal hosts to `keepPerHost` ports before probing.
 */
export function filterRotatingPortFarms(
	candidates,
	{ maxPortsPerHost = MAX_PORTS_PER_HOST_FARM, keepPerHost = KEEP_PORTS_PER_HOST } = {}
) {
	const portsByHost = new Map();
	const itemsByHost = new Map();
	for (const c of candidates) {
		if (!c?.host) continue;
		if (!portsByHost.has(c.host)) {
			portsByHost.set(c.host, new Set());
			itemsByHost.set(c.host, []);
		}
		portsByHost.get(c.host).add(c.port);
		itemsByHost.get(c.host).push(c);
	}

	const kept = [];
	let droppedFarmEntries = 0;
	let droppedFarmHosts = 0;
	for (const [host, items] of itemsByHost.entries()) {
		const distinctPorts = portsByHost.get(host)?.size || 0;
		if (distinctPorts > maxPortsPerHost) {
			droppedFarmHosts++;
			droppedFarmEntries += items.length;
			continue;
		}
		items.sort((a, b) => upstreamPriorityScore(a) - upstreamPriorityScore(b));
		for (let i = 0; i < Math.min(keepPerHost, items.length); i++) {
			kept.push(items[i]);
		}
	}
	return { candidates: kept, droppedFarmHosts, droppedFarmEntries };
}

/**
 * Country-fair round-robin selection with high-demand location boost:
 *   Pass 1: Every available country gets up to `minPerCountry` slots fairly.
 *   Pass 2: High-demand countries (`PRIORITY_COUNTRIES`: DE, FR, NL, GB, etc.)
 *           receive up to `priorityMaxPerCountry` slots so 100% of clean
 *           European/popular candidates are tested before bulk leftovers.
 *   Pass 3: Remaining budget is filled globally by `upstreamPriorityScore`.
 */
export function scheduleCountryFairCandidates(
	candidates,
	{
		maxTotal = MAX_CANDIDATES,
		minPerCountry = MIN_PER_COUNTRY,
		priorityCountries = PRIORITY_COUNTRIES,
		priorityMaxPerCountry = PRIORITY_MAX_PER_COUNTRY,
	} = {}
) {
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

	// Pass 1: universal round-robin up to minPerCountry so no small country is starved
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

	// Pass 2: boost high-demand countries (DE, FR, NL, GB, etc.) in round-robin
	if (selected.length < maxTotal && priorityMaxPerCountry > minPerCountry) {
		const prioKeys = priorityCountries.filter((cc) => groups.has(cc));
		for (let round = minPerCountry; round < priorityMaxPerCountry && selected.length < maxTotal; round++) {
			let added = false;
			for (const cc of prioKeys) {
				if (selected.length >= maxTotal) break;
				const list = groups.get(cc);
				const cur = cursors.get(cc) || 0;
				if (cur < list.length) {
					selected.push(list[cur]);
					cursors.set(cc, cur + 1);
					added = true;
				}
			}
			if (!added) break;
		}
	}

	// Pass 3: fill remaining budget with highest-priority remaining candidates
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

function readHttpHeaderBlock(socket, deadlineMs, stash) {
	return new Promise((resolve, reject) => {
		const existingEnd = stash.buf.indexOf("\r\n\r\n");
		if (existingEnd !== -1) {
			const headerStr = stash.buf.subarray(0, existingEnd).toString("latin1");
			stash.buf = stash.buf.subarray(existingEnd + 4);
			return resolve(headerStr);
		}
		const remain = deadlineMs - Date.now();
		if (remain <= 0) return reject(new Error("connect header timeout"));
		const timer = setTimeout(() => {
			cleanup();
			reject(new Error("connect header timeout"));
		}, remain);
		function onData(chunk) {
			stash.buf = Buffer.concat([stash.buf, chunk]);
			if (stash.buf.length > 32768) {
				cleanup();
				return reject(new Error("connect header too large"));
			}
			const idx = stash.buf.indexOf("\r\n\r\n");
			if (idx !== -1) {
				cleanup();
				const headerStr = stash.buf.subarray(0, idx).toString("latin1");
				stash.buf = stash.buf.subarray(idx + 4);
				resolve(headerStr);
			}
		}
		function onEnd(err) {
			cleanup();
			reject(err || new Error("closed during connect header"));
		}
		function cleanup() {
			clearTimeout(timer);
			socket.off("data", onData);
			socket.off("close", onEnd);
			socket.off("end", onEnd);
			socket.off("error", onEnd);
		}
		socket.on("data", onData);
		socket.once("close", onEnd);
		socket.once("end", onEnd);
		socket.once("error", onEnd);
	});
}

async function openProxyTunnel(proxy, targetHost, targetPort, timeoutMs) {
	const deadline = Date.now() + timeoutMs;
	const tcpBudget = Math.min(CONNECT_TIMEOUT_MS, Math.max(300, deadline - Date.now()));
	const socket = net.connect({ host: proxy.host, port: proxy.port });
	socket.setNoDelay(true);

	await new Promise((resolve, reject) => {
		const timer = setTimeout(() => {
			socket.destroy();
			reject(new Error("connect timeout"));
		}, tcpBudget);
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

			const headerStr = await readHttpHeaderBlock(socket, deadline, stash);
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

async function httpsGetViaProxy(
	proxy,
	{ host, path: reqPath, headers = {}, connectTimeoutMs = null, timeoutMs = PROBE_TIMEOUT_MS, earlyClassifier = null, tlsOptions = {} } = {}
) {
	const started = Date.now();
	const rawSocket = await openProxyTunnel(proxy, host, 443, connectTimeoutMs ?? timeoutMs);
	const remain = Math.max(400, timeoutMs - (Date.now() - started));

	return await new Promise((resolve, reject) => {
		let settled = false;
		const tlsSocket = tls.connect({
			socket: rawSocket,
			servername: host,
			ALPNProtocols: ["http/1.1"],
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

function extractIpFromHttpResponse(txt) {
	if (!/^HTTP\/1\.[01] 200\b/.test(txt || "")) return null;
	const sep = txt.indexOf("\r\n\r\n");
	if (sep < 0) return null;
	let body = txt.slice(sep + 4).trim();
	if (!body) return null;
	if (body.includes("{")) {
		const idx = body.indexOf("{");
		const end = body.indexOf("}", idx);
		if (end > idx) {
			try {
				const ip = String(JSON.parse(body.slice(idx, end + 1))?.ip || "").trim();
				if (net.isIP(ip)) return ip;
			} catch {}
		}
	}
	const lines = body.split(/\r?\n/).map((s) => s.trim()).filter(Boolean);
	for (const line of lines) {
		if (net.isIP(line)) return line;
	}
	return null;
}

async function probeExitIpOnce(candidate, echoTarget, { timeoutMs = PROBE_TIMEOUT_MS, tlsOptions = {} } = {}) {
	const res = await httpsGetViaProxy(candidate, {
		host: echoTarget.host,
		path: echoTarget.path,
		headers: { "User-Agent": "DevCopProxies/2.0", Accept: echoTarget.accept || "*/*" },
		timeoutMs,
		tlsOptions,
		earlyClassifier: (txt) => (extractIpFromHttpResponse(txt) ? true : null),
	});
	const ip = extractIpFromHttpResponse(res.text || "");
	return ip ? { ip, latencyMs: res.latencyMs } : null;
}

async function lookupExitCountry(exitIp) {
	if (!exitIp) return null;
	if (geoCache.has(exitIp)) return geoCache.get(exitIp);

	const job = (async () => {
		// Primary: GeoJS
		try {
			const ctrl = new AbortController();
			const gt = setTimeout(() => ctrl.abort(), 2_500);
			try {
				const gr = await fetch(`https://get.geojs.io/v1/ip/geo/${encodeURIComponent(exitIp)}.json`, { signal: ctrl.signal });
				if (gr.ok) {
					const gd = await gr.json();
					const cc = normalizeCountry(gd?.country_code);
					if (cc) {
						return {
							country: cc,
							country_name: countryNameEn(cc, gd?.country),
							city: gd?.city && String(gd.city).trim() ? String(gd.city).trim() : null,
						};
					}
				}
			} finally {
				clearTimeout(gt);
			}
		} catch {}

		// Secondary fallback: api.country.is
		try {
			const ctrl = new AbortController();
			const gt = setTimeout(() => ctrl.abort(), 2_500);
			try {
				const cr = await fetch(`https://api.country.is/${encodeURIComponent(exitIp)}`, { signal: ctrl.signal });
				if (cr.ok) {
					const cd = await cr.json();
					const cc = normalizeCountry(cd?.country);
					if (cc) {
						return { country: cc, country_name: countryNameEn(cc), city: null };
					}
				}
			} finally {
				clearTimeout(gt);
			}
		} catch {}

		return null;
	})();

	geoCache.set(exitIp, job);
	const resolved = await job;
	if (!resolved) geoCache.delete(exitIp);
	return resolved;
}

/**
 * Verify a single candidate on real TLS 443 (HTTPS IP-echo + `gemini.google.com/app`).
 * - Requires a real verified `exitIp` (never fabricates `exit_ip = host`).
 * - When `exitIp !== candidate.host`, performs a 2nd independent HTTPS IP-echo
 *   check to reject per-connection rotating pools while preserving fixed-exit
 *   NAT / Cloudflare WARP / Cloud VPS proxies that pass Gemini cleanly.
 */
export async function verifyCandidate(candidate, options = {}) {
	const hasExplicitTimeout = options && options.timeoutMs !== undefined;
	const timeoutMs = hasExplicitTimeout ? Number(options.timeoutMs) : PROBE_TIMEOUT_MS;
	const geminiTimeoutMs = hasExplicitTimeout ? timeoutMs : Math.max(timeoutMs, GEMINI_TIMEOUT_MS);
	const tlsOptions = options?.tlsOptions || {};
	const targets = options?.targets || {};

	const targetIdx = echoCursor++ % IP_ECHO_TARGETS.length;
	const primaryEcho = targets.ipifyHost
		? { host: targets.ipifyHost, path: "/?format=json", accept: "application/json" }
		: IP_ECHO_TARGETS[targetIdx];
	const secondaryEcho = targets.ipifyHost
		? primaryEcho
		: IP_ECHO_TARGETS[(targetIdx + 1) % IP_ECHO_TARGETS.length];
	const geminiHost = targets.geminiHost || "gemini.google.com";

	const [echoRes, geminiRes] = await Promise.allSettled([
		probeExitIpOnce(candidate, primaryEcho, { timeoutMs, tlsOptions }),
		httpsGetViaProxy(candidate, {
			host: geminiHost,
			path: "/app",
			headers: { Accept: "text/html,application/xhtml+xml", "Accept-Language": "en-US,en;q=0.9" },
			connectTimeoutMs: timeoutMs,
			timeoutMs: geminiTimeoutMs,
			tlsOptions,
			earlyClassifier: classifyGeminiHttp,
		}),
	]);

	let exitIp = echoRes.status === "fulfilled" && echoRes.value ? echoRes.value.ip : null;
	let latencyMs = echoRes.status === "fulfilled" && echoRes.value ? echoRes.value.latencyMs : null;

	// If primary echo target failed or rate-limited while Gemini succeeded, retry once on secondary echo target
	if (!exitIp && !targets.ipifyHost && geminiRes.status === "fulfilled") {
		try {
			const fallbackEcho = await probeExitIpOnce(candidate, secondaryEcho, { timeoutMs, tlsOptions });
			if (fallbackEcho?.ip) {
				exitIp = fallbackEcho.ip;
				latencyMs = fallbackEcho.latencyMs;
			}
		} catch {}
	}

	// Never publish a proxy whose real exit IP could not be verified or exits on Cloudflare/WARP
	if (!exitIp || isCloudflareEdgeIp(exitIp)) return null;

	let geminiVerdict = { reachable: false, google_ok: false, gemini_ok: false };
	if (geminiRes.status === "fulfilled") {
		geminiVerdict = geminiRes.value.verdict || classifyGeminiHttp(geminiRes.value.text || "") || (
			/^HTTP\/1\.[01] 200\b/.test(geminiRes.value.text || "")
				? { reachable: true, google_ok: true, gemini_ok: true }
				: geminiVerdict
		);
		if (latencyMs === null && geminiVerdict.reachable) latencyMs = geminiRes.value.latencyMs;
	}

	// 2-Probe Exit Stability Verification on multi-hop / NAT servers (`exitIp !== host`):
	// Rejects country-hopping per-connection rotators (`ip2 !== ip1`) and domestic IR/CN
	// hairpin relays while keeping clean fixed-exit NAT / Cloud servers (`ip2 === ip1`).
	if (exitIp !== candidate.host && targets.stabilityCheck !== false) {
		if (candidate.country && EXCLUDED_RELAY_ENTRY_COUNTRIES.has(candidate.country)) return null;
		try {
			const confirmEcho = await probeExitIpOnce(candidate, secondaryEcho, { timeoutMs, tlsOptions });
			if (!confirmEcho?.ip || confirmEcho.ip !== exitIp) {
				return null;
			}
		} catch {
			return null;
		}
		if (targets.geoLookup !== false) {
			const entryGeo = await lookupExitCountry(candidate.host);
			if (entryGeo?.country && EXCLUDED_RELAY_ENTRY_COUNTRIES.has(entryGeo.country)) {
				return null;
			}
		}
	}

	let exitCountry = candidate.country;
	let exitCountryName = candidate.country_name;
	let exitCity = candidate.city;
	if ((exitIp !== candidate.host || !exitCountry) && targets.geoLookup !== false) {
		const geo = await lookupExitCountry(exitIp);
		if (geo?.country) {
			exitCountry = geo.country;
			exitCountryName = geo.country_name || exitCountryName;
			exitCity = geo.city || (exitCountry === candidate.country ? candidate.city : null);
		} else if (exitIp !== candidate.host) {
			// Do not keep an unverified country tag when exit IP differs from entry host
			return null;
		}
	}
	if (!exitCountry || EXCLUDED_COUNTRIES.has(exitCountry)) return null;
	if (candidate.org && /\bcloudflare\b/i.test(candidate.org) && exitIp !== candidate.host) return null;

	return {
		protocol: candidate.protocol,
		username: candidate.username || null,
		password: candidate.password || null,
		host: candidate.host,
		port: candidate.port,
		timeout: Number(((latencyMs ?? timeoutMs) / 1000).toFixed(3)),
		exit_ip: exitIp,
		https: true,
		google_ok: geminiVerdict.google_ok === true,
		gemini_ok: geminiVerdict.gemini_ok === true,
		blocklisted: false,
		hosting: candidate.hosting,
		anonymity: candidate.anonymity,
		uptime: candidate.uptime,
		asn: candidate.org ? { autonomous_system_organization: candidate.org } : undefined,
		geolocation: {
			country: {
				iso_code: exitCountry,
				...(exitCountryName ? { names: { en: exitCountryName } } : {}),
			},
			...(exitCity ? { city: { names: { en: exitCity } } } : {}),
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

/**
 * Cap duplicate ports per host, duplicate protocols on the exact same `host:port`
 * (preferring `socks5` > `http` > `socks4` within the same quality tier),
 * and duplicate entries sharing the same `exit_ip` so every published row
 * represents an independent fixed-exit server.
 */
export function deduplicateVerifiedPool(
	sortedList,
	{ maxPerHost = MAX_VERIFIED_PER_HOST, maxPerExitIp = MAX_VERIFIED_PER_EXIT_IP } = {}
) {
	const protoRank = (p) => (p.protocol === "socks5" ? 0 : p.protocol === "http" ? 1 : 2);
	const tierOf = (p) => (p.gemini_ok ? 0 : p.google_ok ? 1 : 2);
	const bestForHostPort = new Map();
	for (const p of sortedList) {
		const hpKey = `${p.host}:${p.port}`;
		const prev = bestForHostPort.get(hpKey);
		if (!prev || tierOf(p) < tierOf(prev) || (tierOf(p) === tierOf(prev) && protoRank(p) < protoRank(prev))) {
			bestForHostPort.set(hpKey, p);
		}
	}
	const seenHostPort = new Set();
	const hostCounts = new Map();
	const exitCounts = new Map();
	const out = [];
	for (const item of sortedList) {
		const hpKey = `${item.host}:${item.port}`;
		if (seenHostPort.has(hpKey)) continue;
		const p = bestForHostPort.get(hpKey) || item;
		const hCount = hostCounts.get(p.host) || 0;
		if (hCount >= maxPerHost) continue;
		const exitKey = p.exit_ip || p.host;
		const eCount = exitCounts.get(exitKey) || 0;
		if (eCount >= maxPerExitIp) continue;
		seenHostPort.add(hpKey);
		hostCounts.set(p.host, hCount + 1);
		exitCounts.set(exitKey, eCount + 1);
		out.push(p);
	}
	return out;
}

async function fetchFeed(feed) {
	const controller = new AbortController();
	const timer = setTimeout(() => controller.abort(), FETCH_TIMEOUT_MS);
	try {
		const res = await fetch(feed.url, {
			signal: controller.signal,
			headers: { "User-Agent": "DevCop-Proxy-Aggregator/2.1" },
		});
		if (!res.ok) throw new Error(`HTTP ${res.status}`);
		const data = await res.json();
		const rows = Array.isArray(data)
			? data
			: Array.isArray(data?.proxies)
				? data.proxies
				: Array.isArray(data?.data)
					? data.data
					: [];
		return { name: feed.name, rows };
	} finally {
		clearTimeout(timer);
	}
}

export async function runCollection({
	outDir = process.cwd(),
	feeds = UPSTREAM_FEEDS,
	carryForwardUrl = feeds === UPSTREAM_FEEDS ? CARRY_FORWARD_URL : "",
} = {}) {
	const startedAt = new Date();
	const activeFeeds = carryForwardUrl
		? [{ name: "carry_forward", url: carryForwardUrl, carryForward: true, defaultHttps: true }, ...feeds]
		: [...feeds];
	console.log(`[collect] Fetching ${activeFeeds.length} feeds...`);

	const settled = await Promise.allSettled(activeFeeds.map(fetchFeed));
	const byKey = new Map();
	const feedSummary = [];

	for (let i = 0; i < settled.length; i++) {
		const res = settled[i];
		const feedCfg = activeFeeds[i];
		const feedName = feedCfg.name;
		if (res.status !== "fulfilled") {
			console.warn(`[collect] Feed ${feedName} failed: ${res.reason?.message || res.reason}`);
			feedSummary.push({ name: feedName, ok: false, count: 0 });
			continue;
		}
		let accepted = 0;
		for (const raw of res.value.rows) {
			const entry = normalizeUpstreamEntry(raw, {
				defaultHttps: feedCfg.defaultHttps ?? null,
				carryForward: Boolean(feedCfg.carryForward),
			});
			if (!entry) continue;
			accepted++;
			const key = `${entry.protocol}://${entry.host}:${entry.port}`;
			const existing = byKey.get(key);
			if (!existing) {
				byKey.set(key, entry);
			} else {
				existing.carried_forward = existing.carried_forward || entry.carried_forward;
				existing.upstream_gemini = existing.upstream_gemini || entry.upstream_gemini;
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

	const rawUnique = [...byKey.values()];
	const { candidates: cleanCandidates, droppedFarmHosts, droppedFarmEntries } = filterRotatingPortFarms(rawUnique);
	const scheduled = scheduleCountryFairCandidates(cleanCandidates);
	const inputCountries = new Set(scheduled.map((c) => c.country).filter(Boolean)).size;
	console.log(
		`[collect] Deduplicated: ${rawUnique.length} → Clean: ${cleanCandidates.length} (dropped ${droppedFarmEntries} entries across ${droppedFarmHosts} rotating port-farm hosts) → Scheduled ${scheduled.length} across ${inputCountries} countries (concurrency=${CONCURRENCY})`
	);

	const verified = [];
	let cursor = 0;
	let testedCount = 0;
	const wallDeadline = startedAt.getTime() + MAX_WALL_TIME_MS;
	async function worker() {
		while (cursor < scheduled.length && Date.now() < wallDeadline) {
			const idx = cursor++;
			testedCount++;
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

	const sorted = deduplicateVerifiedPool(sortVerifiedProxies(verified));
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
		candidates_total: cleanCandidates.length,
		rotating_farm_dropped: droppedFarmEntries,
		candidates_tested: testedCount,
		working_https: sorted.length,
		unique_hosts: new Set(sorted.map((p) => p.host)).size,
		unique_exit_ips: new Set(sorted.map((p) => p.exit_ip || p.host)).size,
		single_hop: sorted.filter((p) => !p.exit_ip || p.exit_ip === p.host).length,
		fixed_nat: sorted.filter((p) => p.exit_ip && p.exit_ip !== p.host).length,
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
		`[collect] Done in ${stats.duration_sec}s: ${stats.working_https} fixed proxies (${stats.unique_hosts} unique hosts · ${stats.gemini_ok} Gemini · ${stats.google_ok} Google) across ${stats.countries_count} countries.`
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
