GO ?= go
VERSION ?= dev

.PHONY: build test verify test-all plugin-dir plugin-package

build:
	$(GO) build -trimpath -ldflags '-X main.version=$(VERSION)' -o bin/helm-schema ./cmd/helm-schema

test:
	$(GO) test ./...

verify:
	@rg -n '\b(sorry|admit|axiom)\b' formal/HelmSchema.lean \
		formal/HelmSchema formal/Verify formal/Tests --glob '*.lean'; \
		rg_status=$$?; \
		test "$$rg_status" -eq 1
	cd formal && lake build && lake build axiomAudit && lake test
	HELM_SCHEMA_FORMAL_VERIFY="$(CURDIR)/formal/.lake/build/bin/verify" \
		$(GO) test -count=1 -v ./internal/formalconformance

test-all: test verify

plugin-dir: build
	install -d .dist/schema/bin
	install -m 0755 bin/helm-schema .dist/schema/bin/helm-schema
	install -m 0644 plugin.yaml .dist/schema/plugin.yaml
	install -m 0755 install.sh .dist/schema/install.sh
	install -m 0644 install.ps1 .dist/schema/install.ps1

plugin-package: plugin-dir
	helm plugin package --sign=false --destination .dist .dist/schema
