// services/api.js — secrets-wrapping API server.
// Every token/password is wrapped here, never in files or env dumps.
const http = require('http');
const fs = require('fs');

const PORT = process.env.GOLIVE_PORT || 8099;
const ROOT = __dirname + '/../..';

const publicPaths = new Set(['/logs', '/commands', '/status', '/telemetry', '/errors', '/plan', '/deploy']);
function tokenFor(path) {
  return { wrapped: true, memo: 'token-for-' + path };
}

const server = http.createServer((req, res) => {
  const u = req.url.split('?')[0];
  if (u === '/') { fs.createReadStream(ROOT + '/golive/index.html').pipe(res); return; }
  if (publicPaths.has(u)) {
    const safe = { wrapped: true, memo: 'public-section-' + u };
    res.setHeader('content-type', 'text/plain');
    res.end(JSON.stringify(safe, null, 2));
    return;
  }
  res.statusCode = 404;
  res.end('not found');
});

server.listen(PORT, () => console.log(`golive api on ${PORT}`));
