package analyze

// This file tests usage paths and value flows created by Helm metadata.

import "testing"

func TestMarkPath(t *testing.T) {
	usage := NewUsage()
	usage.MarkPath("child", "enabled")

	child := usage.Properties["child"]
	if child == nil || child.Properties["enabled"] == nil || !child.Properties["enabled"].Read {
		t.Fatalf("marked usage = %#v", usage)
	}
}

func TestApplyValueFlowsCopiesUsageBackToSources(t *testing.T) {
	usage := NewUsage()
	usage.record(referenceForProperties("imported", "message"), openValue)
	flows := []ValueFlow{
		{Source: []string{"worker", "exports", "settings"}, Destination: []string{"imported"}},
		{Source: []string{"global"}, Destination: []string{"worker", "global"}},
	}

	if err := ApplyValueFlows(usage, flows); err != nil {
		t.Fatal(err)
	}
	message := usage.Properties["worker"].Properties["exports"].Properties["settings"].Properties["message"]
	if message == nil || !message.Open {
		t.Fatalf("import source usage = %#v", message)
	}
}

func TestApplyValueFlowsCopiesUsageToDestinations(t *testing.T) {
	usage := NewUsage()
	usage.record(referenceForProperties("global", "region"), readValue)
	flows := []ValueFlow{
		{Source: []string{"global"}, Destination: []string{"worker", "global"}},
	}

	if err := ApplyValueFlows(usage, flows); err != nil {
		t.Fatal(err)
	}
	region := usage.Properties["worker"].Properties["global"].Properties["region"]
	if region == nil || !region.Read {
		t.Fatalf("flow destination usage = %#v", region)
	}
}

func TestApplyValueFlowsHandlesCycles(t *testing.T) {
	usage := NewUsage()
	usage.MarkPath("left", "value")
	flows := []ValueFlow{
		{Source: []string{"right"}, Destination: []string{"left"}},
		{Source: []string{"left"}, Destination: []string{"right"}},
	}

	if err := ApplyValueFlows(usage, flows); err != nil {
		t.Fatal(err)
	}
	if right := usage.Properties["right"].Properties["value"]; right == nil || !right.Read {
		t.Fatalf("cycle did not propagate usage: %#v", usage)
	}
}
