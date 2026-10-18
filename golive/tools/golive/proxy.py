#!/usr/bin/env python3
"""golive proxy.py — nginx/systemd egress proxy (no user-home access)."""
import os, sys

port = os.environ.get("GOLIVE_PORT", "9000")
print(f"golive proxy listening on {port}")
sys.stdout.flush()
while True:
    pass
