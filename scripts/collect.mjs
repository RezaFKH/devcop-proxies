/**
 * Dev.Cop Proxies — Zero-dependency multi-source proxy aggregator & verifier.
 *
 * Pulls already-verified candidates from independent public feeds (never blind
 * port-scanning), schedules candidates fairly across EVERY available country,
 * performs real SOCKS5 / SOCKS4 / HTTP CONNECT + verified TLS 443 handshakes
 * against `api.ipify.org` and `gemini.google.com`, and emits `proxies.json` in
 * the exact schema consumed by Dev.Cop Panel.
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

export const UPSTREAM_FEEDS = [
	{ name: "maximilianfeix", url: "https://raw.githubusercontent.com/maximilianfeix/free-proxy-list/main/proxies.json" },
	{ name: "proxyscrape", url: "https://raw.githubusercontent.com/ProxyScrape/free-proxy-list/main/proxies/all/data.json" },
	{ name: "proxifly", url: "https://raw.githubusercontent.com/proxifly/free-proxy-list/main/proxies/all/data.json" },
	{ name: "hproxy", url: "https://raw.githubusercontent.com/hproxy-com/free-proxy-list/main/live.json" },
	{ name: "xyzs996", url: "https://raw.githubusercontent.com/xyzs996/free-proxy-health-list/main/proxies/all/data.json" },
	{ name: "litportnet", url: "https://raw.githubusercontent.com/litportnet/free-proxy-list/live/proxies/all.json" },
	{ name: "monosans", url: "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies.json" },
	{ name: "xyzs996", url: "https://raw.githubusercontent.com/xyzs996/free-proxy-health-list/main/proxies/stability/stable/data.json" },
	{ name: "litportnet", url: "https://raw.githubusercontent.com/litportnet/free-proxy-list/live/proxies/stable.json" },
	{ name: "proxyscrape", url: "https://raw.githubusercontent.com/ProxyScrape/free-proxy-list/main/proxies/all/data.json" },
	{ name: "vakhov", url: "https://raw.githubusercontent.com/vakhov/fresh-proxy-list/master/proxylist.json" },
];

const FETCH_TIMEOUT_MS = Number(process.env.FETCH_TIMEOUT_MS || 15_000);
export const PRIORITY_COUNTRIES = [
	"DE", "FR", "NL", "GB", "CH", "SE", "FI", "AT",
	"IT", "ES", "PL", "TR", "CA", "AE", "JP", "SG", "US",
];

const IP_ECHO_TARGETS = [
	{ host: "api.ipify.org", path: "/?format=json", accept: "application/json" },
	{ host: "checkip.amazonaws.com", path: "/", accept: "text/plain" },
	{ host: "icanhazip.com", path: "/", accept: "text/plain" },
];

const FETCH_TIMEOUT_MS = Number(process.env.FETCH_TIMEOUT_MS || 18_000);
const CONNECT_TIMEOUT_MS = Number(process.env.CONNECT_TIMEOUT_MS || 2_200);
const PROBE_TIMEOUT_MS = Number(process.env.PROBE_TIMEOUT_MS || 3_500);
const CONCURRENCY = Number(process.env.CONCURRENCY || 60);
const MAX_CANDIDATES = Number(process.env.MAX_CANDIDATES || 3_600);
const CONCURRENCY = Number(process.env.CONCURRENCY || 110);
const MAX_CANDIDATES = Number(process.env.MAX_CANDIDATES || 6_500);
const MIN_PER_COUNTRY = Number(process.env.MIN_PER_COUNTRY || 40);
const PRIORITY_MAX_PER_COUNTRY = Number(process.env.PRIORITY_MAX_PER_COUNTRY || 400);
const MAX_PORTS_PER_HOST_FARM = Number(process.env.MAX_PORTS_PER_HOST_FARM || 4);
const KEEP_PORTS_PER_HOST = Number(process.env.KEEP_PORTS_PER_HOST || 2);
const MAX_VERIFIED_PER_HOST = Number(process.env.MAX_VERIFIED_PER_HOST || 2);
const MAX_VERIFIED_PER_EXIT_IP = Number(process.env.MAX_VERIFIED_PER_EXIT_IP || 2);

const REGION_NAMES = typeof Intl !== "undefined" && Intl.DisplayNames ? new Intl.DisplayNames(["en"], { type: "region" }) : null;

const NON_THREAT_VALUES = new Set(["", "none", "unknown", "clean", "null", "false", "low", "ok"]);

const CF_IPV4_CIDRS = [
	[0x6715f400, 22], [0x6716c800, 22], [0x671f0400, 22], [0x68100000, 13],
	[0x68180000, 14], [0x6ca2c000, 18], [0x83004800, 22], [0x8d654000, 18],
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
	return /^[A-Z]{2}$/.test(code) ? code : null;
	return /^[A-Z]{2}$/.test(code) && code !== "ZZ" && code !== "XX" ? code : null;
}

function countryNameEn(code, explicitName = null) {
export function normalizeUpstreamEntry(entry) {
	if (!entry || typeof entry !== "object") return null;

	// vakhov stores protocol booleans ("socks5": "1", "socks4": "1", "http": "1", "ssl": "1")
	// hproxy stores `protocols: ["socks5", "https", ...]`
	let protoArrayHttps = null;
	let hintedProto = entry.protocol || entry.ptype || null;
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
		}
	}

	// vakhov stores protocol booleans ("socks5": "1", "socks4": "1", "http": "1", "ssl": "1")
	let vakhovHttps = null;
	if (!hintedProto) {
		if (entry.socks5 === "1" || entry.socks5 === 1 || entry.socks5 === true) hintedProto = "socks5";
		else if (entry.socks4 === "1" || entry.socks4 === 1 || entry.socks4 === true) hintedProto = "socks4";
		else if (entry.http === "1" || entry.http === 1 || entry.ssl === "1" || entry.ssl === 1) hintedProto = "http";
		else if (entry.ssl === "1" || entry.ssl === 1) {
			hintedProto = "http";
			vakhovHttps = true;
		} else if (entry.http === "1" || entry.http === 1) {
			hintedProto = "http";
			if (entry.ssl === "0" || entry.ssl === 0) vakhovHttps = false;
		}
	}

	const rawProtoLower = String(entry.protocol || entry.ptype || "").trim().toLowerCase();
	let host = String(entry.ip || entry.host || entry.address || "").trim().replace(/^\[|\]$/g, "");
	let port = Number(entry.port);
	let parsed = null;
	// Prefer numeric IPv4/IPv6 literal when `entry.ip` is available (avoids stale rDNS hostnames)
	if (entry.ip && net.isIP(String(entry.ip).trim())) host = String(entry.ip).trim();

	// Reject Cloudflare CDN Anycast IPs (reverse proxies, never forward tunnels)
	if (isCloudflareEdgeIp(host)) return null;

	const protocol = normalizeProtocol(hintedProto || parsed?.protocol || "socks5");
	const geo = entry.geolocation && typeof entry.geolocation === "object" ? entry.geolocation : {};
	const country =
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

	// Skip HTTP proxies explicitly proved unable to tunnel HTTPS
	if (protocol === "http" && https === false) return null;

	const blocklisted =
		entry.blocklisted === true ||
		(typeof entry.threat === "string" && entry.threat.trim() !== "" && entry.threat.trim().toLowerCase() !== "none");
	if (blocklisted) return null;

	const hosting =
		typeof entry.hosting === "boolean"
			? entry.hosting
		finiteNonNegative(entry.uptime_percent) ??
		finiteNonNegative(entry.reliabilityScore);

	// `xyzs996` uses `threat: "unknown"` on clean proxies; `maximilianfeix` sets
	// `blocklisted: true` on datacenter ASNs (Hetzner DE, OVH FR, Google Cloud) even
	// when `sites.google === true` or `uptime_24h >= 60`. Keep explicit abuse
	// blocklists dropped while allowing Google-verified/high-uptime cloud hosts.
	const threatStr = typeof entry.threat === "string" ? entry.threat.trim().toLowerCase() : "";
	const hasRealThreat = threatStr !== "" && !NON_THREAT_VALUES.has(threatStr);
	const trustedCloudHost = hosting === true && (entry.sites?.google === true || entry.google_ok === true || (uptime !== null && uptime >= 60));
	const blocklisted = hasRealThreat || (entry.blocklisted === true && !trustedCloudHost);
	if (blocklisted) return null;

	const org =
		entry.asn?.autonomous_system_organization ||
		geo?.asn?.autonomous_system_organization ||
	let score = 0;
	if (c.upstream_google) score -= 1000;
	if (c.upstream_https === true) score -= 300;
	if (c.protocol === "socks5") score -= 120;
	if (c.hosting === false) score -= 150;
	if (c.protocol === "socks5") score -= 140;
	if (c.hosting === false) score -= 120;
	if (c.anonymity === "elite") score -= 40;
	if (c.uptime !== null) score -= Math.min(100, c.uptime);
	score += Math.min(50, (c.upstream_timeout ?? 5) * 10);
}

/**
 * Country-fair round-robin selection: guarantees every available country gets
 * representation (up to `minPerCountry` first, then global fill to `maxTotal`).
 * Strip port-multiplexed rotating backconnect farms (such as `45.74.31.40..47`
 * advertising hundreds of ports on one IP whose exit country changes every
 * minute) and cap normal hosts to `keepPerHost` ports before probing.
 */
export function scheduleCountryFairCandidates(candidates, { maxTotal = MAX_CANDIDATES, minPerCountry = MIN_PER_COUNTRY } = {}) {
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
	const selected = [];
	const cursors = new Map([...groups.keys()].map((k) => [k, 0]));

	// Pass 1: round-robin up to minPerCountry so no small country is starved
	// Pass 1: universal round-robin up to minPerCountry so no small country is starved
	for (let round = 0; round < minPerCountry && selected.length < maxTotal; round++) {
		let added = false;
		for (const [key, list] of groups.entries()) {
		if (!added) break;
	}

	// Pass 2: fill remaining budget with highest-priority remaining candidates
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

		const timer = setTimeout(() => {
			socket.destroy();
			reject(new Error("connect timeout"));
		}, Math.max(200, deadline - Date.now()));
		}, tcpBudget);
		socket.once("connect", () => {
			clearTimeout(timer);
			resolve();
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
			const headerStr = await readHttpHeaderBlock(socket, deadline, stash);
			const status = Number(headerStr.split("\r\n")[0].match(/HTTP\/1\.[01] (\d{3})/)?.[1] || 0);
			if (status !== 200) throw new Error(`HTTP CONNECT ${status}`);
		}
		const tlsSocket = tls.connect({
			socket: rawSocket,
			servername: host,
			ALPNProtocols: ["http/1.1"],
			rejectUnauthorized: true,
			...tlsOptions,
		});
	});
}

/** Verify a single candidate on real TLS 443 (`api.ipify.org` + `gemini.google.com`). */
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
export async function verifyCandidate(candidate, { timeoutMs = PROBE_TIMEOUT_MS, tlsOptions = {}, targets = {} } = {}) {
	const ipifyHost = targets.ipifyHost || "api.ipify.org";
	const targetIdx = echoCursor++ % IP_ECHO_TARGETS.length;
	const primaryEcho = targets.ipifyHost
		? { host: targets.ipifyHost, path: "/?format=json", accept: "application/json" }
		: IP_ECHO_TARGETS[targetIdx];
	const secondaryEcho = targets.ipifyHost
		? primaryEcho
		: IP_ECHO_TARGETS[(targetIdx + 1) % IP_ECHO_TARGETS.length];
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
	const [echoRes, geminiRes] = await Promise.allSettled([
		probeExitIpOnce(candidate, primaryEcho, { timeoutMs, tlsOptions }),
		httpsGetViaProxy(candidate, {
			host: geminiHost,
			path: "/app",
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
			if (exitIp) latencyMs = ipifyRes.value.latencyMs;
		}
		} catch {}
	}

	// Never publish a proxy whose real exit IP could not be verified
	if (!exitIp) return null;

	let geminiVerdict = { reachable: false, google_ok: false, gemini_ok: false };
	if (geminiRes.status === "fulfilled") {
		geminiVerdict = geminiRes.value.verdict || classifyGeminiHttp(geminiRes.value.text || "") || (
		if (latencyMs === null && geminiVerdict.reachable) latencyMs = geminiRes.value.latencyMs;
	}

	if (!exitIp && !geminiVerdict.reachable) return null;
	// 2-Probe Exit Stability Verification on multi-hop / NAT servers (`exitIp !== host`):
	// Rejects country-hopping per-connection rotators (`ip2 !== ip1`) while keeping
	// fixed-exit NAT / Cloudflare WARP / Cloud servers (`ip2 === ip1`) intact for Gemini.
	if (exitIp !== candidate.host && targets.stabilityCheck !== false) {
		try {
			const confirmEcho = await probeExitIpOnce(candidate, secondaryEcho, { timeoutMs, tlsOptions });
			if (!confirmEcho?.ip || confirmEcho.ip !== exitIp) {
				return null;
			}
		} catch {
			return null;
		}
	}

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
	if (!exitCountry) return null;

	return {
		protocol: candidate.protocol,
		host: candidate.host,
		port: candidate.port,
		timeout: Number(((latencyMs ?? timeoutMs) / 1000).toFixed(3)),
		exit_ip: exitIp || candidate.host,
		exit_ip: exitIp,
		https: true,
		google_ok: geminiVerdict.google_ok === true,
		gemini_ok: geminiVerdict.gemini_ok === true,
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
			country: {
				iso_code: exitCountry,
				...(exitCountryName ? { names: { en: exitCountryName } } : {}),
			},
			...(exitCity ? { city: { names: { en: exitCity } } } : {}),
		},
	};
}
	});
}

/**
 * Cap duplicate ports per host and duplicate entries sharing the same `exit_ip`
 * so every published row represents an independent fixed-exit server.
 */
export function deduplicateVerifiedPool(
	sortedList,
	{ maxPerHost = MAX_VERIFIED_PER_HOST, maxPerExitIp = MAX_VERIFIED_PER_EXIT_IP } = {}
) {
	const hostCounts = new Map();
	const exitCounts = new Map();
	const out = [];
	for (const p of sortedList) {
		const hCount = hostCounts.get(p.host) || 0;
		if (hCount >= maxPerHost) continue;
		const exitKey = p.exit_ip || p.host;
		const eCount = exitCounts.get(exitKey) || 0;
		if (eCount >= maxPerExitIp) continue;
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
			headers: { "User-Agent": "DevCop-Proxy-Aggregator/1.0" },
			headers: { "User-Agent": "DevCop-Proxy-Aggregator/2.0" },
		});
		if (!res.ok) throw new Error(`HTTP ${res.status}`);
		const data = await res.json();
		feedSummary.push({ name: feedName, ok: true, count: accepted });
	}

	const uniqueCandidates = [...byKey.values()];
	const scheduled = scheduleCountryFairCandidates(uniqueCandidates);
	const rawUnique = [...byKey.values()];
	const { candidates: cleanCandidates, droppedFarmHosts, droppedFarmEntries } = filterRotatingPortFarms(rawUnique);
	const scheduled = scheduleCountryFairCandidates(cleanCandidates);
	const inputCountries = new Set(scheduled.map((c) => c.country).filter(Boolean)).size;
	console.log(`[collect] Deduplicated: ${uniqueCandidates.length} → Scheduled ${scheduled.length} across ${inputCountries} countries (concurrency=${CONCURRENCY})`);
	console.log(
		`[collect] Deduplicated: ${rawUnique.length} → Clean: ${cleanCandidates.length} (dropped ${droppedFarmEntries} entries across ${droppedFarmHosts} rotating port-farm hosts) → Scheduled ${scheduled.length} across ${inputCountries} countries (concurrency=${CONCURRENCY})`
	);

	const verified = [];
	let cursor = 0;
	}
	await Promise.all(Array.from({ length: Math.min(CONCURRENCY, Math.max(1, scheduled.length)) }, () => worker()));

	const sorted = sortVerifiedProxies(verified);
	const sorted = deduplicateVerifiedPool(sortVerifiedProxies(verified));
	if (sorted.length === 0) {
		throw new Error("Zero working HTTPS proxies verified — aborting publish to preserve last healthy snapshot.");
	}
	const stats = {
		updated_at: new Date().toISOString(),
		duration_sec: Number(((Date.now() - startedAt.getTime()) / 1000).toFixed(1)),
		candidates_total: uniqueCandidates.length,
		candidates_total: cleanCandidates.length,
		rotating_farm_dropped: droppedFarmEntries,
		candidates_tested: scheduled.length,
		working_https: sorted.length,
		unique_hosts: new Set(sorted.map((p) => p.host)).size,
		unique_exit_ips: new Set(sorted.map((p) => p.exit_ip || p.host)).size,
		single_hop: sorted.filter((p) => !p.exit_ip || p.exit_ip === p.host).length,
		fixed_nat: sorted.filter((p) => p.exit_ip && p.exit_ip !== p.host).length,
		google_ok: sorted.filter((p) => p.google_ok).length,
		gemini_ok: sorted.filter((p) => p.gemini_ok).length,
		countries_count: Object.keys(countries).filter((c) => c !== "UNK").length,
	await fs.writeFile(path.join(outDir, "stats.json"), JSON.stringify(stats, null, 2) + "\n");

	console.log(
		`[collect] Done in ${stats.duration_sec}s: ${stats.working_https} HTTPS · ${stats.google_ok} Google · ${stats.gemini_ok} Gemini across ${stats.countries_count} countries.`
		`[collect] Done in ${stats.duration_sec}s: ${stats.working_https} fixed proxies (${stats.unique_hosts} unique hosts · ${stats.gemini_ok} Gemini · ${stats.google_ok} Google) across ${stats.countries_count} countries.`
	);
	return { proxies: sorted, stats };
}
