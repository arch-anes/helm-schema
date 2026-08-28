GO ?= go
VERSION ?= dev

.PHONY: build test plugin-dir plugin-package

build:
	$(GO) build -trimpath -ldflags '-X main.version=$(VERSION)' -o bin/helm-schema ./cmd/helm-schema

test:
	$(GO) test ./...

plugin-dir: build
	install -d .dist/schema/bin
	install -m 0755 bin/helm-schema .dist/schema/bin/helm-schema
	install -m 0644 plugin.yaml .dist/schema/plugin.yaml
	install -m 0755 install.sh .dist/schema/install.sh
	install -m 0644 install.ps1 .dist/schema/install.ps1

plugin-package: plugin-dir
	helm plugin package --sign=false --destination .dist .dist/schema
