# Task: Gokujo Cloudflare Integration - Golive Website

## Goal

Create a golive website for the SOPS Cloudflare deployment using the existing
nginx/system-manager infrastructure, with full Gokujo Layer Architecture integration.

## Current State

### Existing Infrastructure (Read & Analyzed)
- `~/projects/system-manager/nginx/` - nginx modular configs
- `~/projects/system-manager/modules/nginx.nix` - nginx module for system-manager
- `~/projects/system-manager/all-services.nix` - main system-manager config
- `~/projects/twitterstorm/tracker/` - Twitter tracker services (ports 8790-8794)
- `~/projects/lean-worker/tools/gokujo/` - Gokujo tools directory

### Existing Nginx Sites
- `tracker-worker.conf` - Twitter tracker workers (ports 8790-8794)
- `tracker-fleet.conf` - Fleet supervisor (port 3329)
- `golive-deck.conf` - Golive control deck (port 3341)
- `golive-branch-base.conf` - Branch base golive (port 38888)

### Gokujo Integration
- `tools/gokujo/Cloudflare/` - Cloudflare API integration
- `tools/gokujo/SOPS/Cloudflare/` - SOPS-based deployment tool
- `tools/gokujo/SOPS/SOPS.lean` - SOPS module for encrypted secrets

## Plan

### 1. Create Golive Website for Cloudflare Layer
- Create `gokujo-cloudflare-golive.conf` nginx config
- Create `gokujo-cloudflare-golive.html` dashboard page
- Integrate with system-manager modules
- Use existing golive infrastructure on ports 3341-3342

### 2. System-Manager Integration
- Add to `nginx.nix` module includes
- Configure backend service for Cloudflare deployment status
- Use Nix-based build system

### 3. Gokujo Layer Architecture
- Map Cloudflare deployment to Gokujo layers:
  - Layer 1: Gokujo Git Layer (path management)
  - Layer 2: SOPS Layer (encrypted secrets)
  - Layer 3: Cloudflare Layer (wrangler deployment)

### 4. Deploy to all 3 accounts
- Account 1: meta-introspector (0xda5130026116ad43)
- Account 2: internal (0xda5240026116ad43)
- Account 3: partners (0xda5360026116ad43)

## Deliverables
- [x] SOPS Cloudflare Integration.lean
- [x] SOPS module
- [ ] Golive nginx website for Cloudflare deployment
- [ ] System-manager nix module
- [ ] Deployment scripts
- [ ] Task documentation
