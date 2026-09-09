"""Bounded direct source retrieval. No agent-controlled network access."""
import hashlib
import ipaddress
import re
import socket
import subprocess
import tempfile
import urllib.request
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit
from .core import now, save
from . import report as rr

MAX_BYTES = 4 * 1024 * 1024
MAX_URLS = 16

class Text(HTMLParser):
    def __init__(self):
        super().__init__(); self.parts = []; self.hidden = 0
    def handle_starttag(self, tag, attrs):
        if tag in ('script', 'style'): self.hidden += 1
    def handle_endtag(self, tag):
        if tag in ('script', 'style'): self.hidden = max(0, self.hidden-1)
        self.parts.append('\n')
    def handle_data(self, data):
        if not self.hidden: self.parts.append(data)

def public_url(url):
    p = urlsplit(url)
    if p.scheme not in ('https', 'http') or not p.hostname or p.username or p.password or p.port not in (None, 80, 443):
        raise ValueError('Source must be an ordinary public HTTP(S) URL')
    addresses = socket.getaddrinfo(p.hostname, p.port or (443 if p.scheme == 'https' else 80))
    if not addresses or any(not ipaddress.ip_address(a[4][0]).is_global for a in addresses):
        raise ValueError('Non-public source address')
    return url

class Redirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        public_url(newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)

def retrieve(url):
    public_url(url)
    req = urllib.request.Request(url, headers={'User-Agent': 'FC-contribution-toolkit/0.1 (source review)'})
    with urllib.request.build_opener(Redirect()).open(req, timeout=20) as response:
        raw = response.read(MAX_BYTES+1)
        if len(raw) > MAX_BYTES: raise ValueError('Source exceeds 4 MiB')
        kind = response.headers.get_content_type()
        final = response.url
    if kind == 'application/pdf' or raw.startswith(b'%PDF'):
        with tempfile.TemporaryDirectory() as temp:
            pdf = Path(temp)/'source.pdf'; pdf.write_bytes(raw)
            proc = subprocess.run(['pdftotext', '-layout', str(pdf), '-'], capture_output=True, timeout=20)
            if proc.returncode: raise ValueError('PDF extraction failed')
            text = proc.stdout.decode(errors='replace')
    else:
        text = raw.decode('utf-8', errors='replace')
        if kind == 'text/html':
            parser = Text(); parser.feed(text); text = ' '.join(parser.parts)
    offset = 0
    anchor = re.fullmatch(r'problem[.-](\d+)', urlsplit(url).fragment, re.IGNORECASE)
    if anchor:
        found = re.search(r'Problem\s+'+anchor[1]+r'\.', text)
        if found: offset = max(0, found.start()-200)
    return {'url': url, 'resolved_url': final, 'retrieved_at': now(),
            'sha256': hashlib.sha256(raw).hexdigest(), 'media_type': kind,
            'passages': text[offset:offset+24000], 'passage_offset': offset, 'truncated': len(text) > 24000}

def cited_urls(files):
    urls = set()
    for raw in files:
        for url in re.findall(r'https?://[^\s<>"\]\)]+', raw.decode(errors='replace')):
            url = url.rstrip('.,;')
            m = re.fullmatch(r'https?://(?:www\.)?erdosproblems.com/(\d+)/?', url)
            urls.add('https://www.erdosproblems.com/latex/'+m[1] if m else url)
    return sorted(urls)

def collect(destination, files, supplied=None):
    destination.mkdir(parents=True, exist_ok=True)
    records = []
    if supplied:
        supplied_files = rr.collect(Path(supplied).resolve(), 'supplied')
        for name, raw in supplied_files.items():
            if len(raw) > MAX_BYTES: raise ValueError('Supplied source exceeds 4 MiB')
            p = destination/name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(raw)
        # Supplied sources are explicit operator evidence, not independently retrieved pages.
        return {'mode': 'supplied', 'coverage': 'available' if supplied_files else 'incomplete', 'records': []}
    urls = cited_urls(files)
    for i, url in enumerate(urls[:MAX_URLS]):
        try:
            record = retrieve(url)
            save(destination/f'source-{i:02d}.json', record)
            records.append({'url': url, 'status': 'retrieved', 'sha256': record['sha256']})
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            records.append({'url': url, 'status': 'unavailable', 'reason': str(error)})
    return {'mode': 'cited', 'coverage': 'available' if urls and len(urls)<=MAX_URLS and
            all(r['status']=='retrieved' for r in records) else 'incomplete', 'records': records,
            'omitted_urls': urls[MAX_URLS:]}
