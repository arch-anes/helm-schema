#!/bin/sh
set -eu

plugin_dir=${HELM_PLUGIN_DIR:?HELM_PLUGIN_DIR is not set}
binary="$plugin_dir/bin/helm-schema"

# Packaged plugins already contain the native executable. A source checkout
# (for example, a Git URL passed to `helm plugin install`) needs to build it.
if [ -x "$binary" ]; then
    exit 0
fi

if ! command -v go >/dev/null 2>&1; then
    echo "helm-schema source installation requires Go; install a packaged release or install Go and retry" >&2
    exit 1
fi

mkdir -p "$plugin_dir/bin"
cd "$plugin_dir"
go build -buildvcs=false -trimpath -o "$binary" ./cmd/helm-schema
chmod 0755 "$binary"
