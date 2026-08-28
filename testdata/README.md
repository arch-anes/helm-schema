# Test fixtures

This directory contains small Helm charts created for this project.

Each fixture isolates a schema rule. The tests assert both accepted and rejected value changes.

`kube-prometheus-stack-88-regression` preserves the dynamic `tpl` and `retentionSize` pattern that exposed nested typo acceptance.

`octoprint-common-29-regression` preserves dynamic service and port names while requiring each port object to use fields supported by the common library.

Full third-party charts do not belong in this directory. They add large licensed copies and change when upstream releases change.

Use temporary copies of upstream charts for acceptance runs. Generation replaces schemas in the selected chart and its unpacked dependencies.
