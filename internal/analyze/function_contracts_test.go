package analyze

import (
	"slices"
	"strings"
	"testing"
)

// helmFunctionNames is the pinned Helm 4.2.4, Sprig 3.3.0, and Go template
// function surface. Keeping the source list separate from the production
// classes makes additions and removals visible in review.
func helmFunctionNames() []string {
	const names = `
abbrev abbrevboth add add1 add1f addf adler32sum ago all and any append atoi
b32dec b32enc b64dec b64enc base bcrypt biggest buildCustomCert call camelcase
cat ceil chunk clean coalesce compact concat contains date dateInZone dateModify
date_in_zone date_modify decryptAES deepCopy deepEqual default derivePassword
dict dig dir div divf duration durationRound empty encryptAES eq ext fail first
float64 floor fromJson fromJsonArray fromToml fromYaml fromYamlArray ge genCA
genCAWithKey genPrivateKey genSelfSignedCert genSelfSignedCertWithKey genSignedCert
genSignedCertWithKey get getHostByName gt has hasKey hasPrefix hasSuffix hello
html htmlDate htmlDateInZone htpasswd include indent index initial initials int
int64 isAbs join js kebabcase keys kindIs kindOf last le len list lookup lower lt
max maxf merge mergeOverwrite min minf mod mul mulf mustAppend mustChunk
mustCompact mustDateModify mustDeepCopy mustFirst mustFromJson mustHas
mustInitial mustLast mustMerge mustMergeOverwrite mustPrepend mustRegexFind
mustRegexFindAll mustRegexMatch mustRegexReplaceAll mustRegexReplaceAllLiteral
mustRegexSplit mustRest mustReverse mustSlice mustToDate mustToJson
mustToPrettyJson mustToRawJson mustToToml mustToYaml mustUniq mustWithout
must_date_modify ne nindent nospace not now omit or osBase osClean osDir osExt
osIsAbs pick pluck plural prepend print printf println quote randAlpha
randAlphaNum randAscii randBytes randInt randNumeric regexFind regexFindAll
regexMatch regexQuoteMeta regexReplaceAll regexReplaceAllLiteral regexSplit
repeat replace required rest reverse round semver semverCompare seq set sha1sum
sha256sum sha512sum shuffle slice snakecase sortAlpha split splitList splitn
squote sub subf substr swapcase ternary title toDate toDecimal toJson
toPrettyJson toRawJson toString toStrings toToml toYaml toYamlPretty tpl trim
trimAll trimPrefix trimSuffix trimall trunc tuple typeIs typeIsLike typeOf uniq
unixEpoch unset until untilStep untitle upper urlJoin urlParse urlquery uuidv4
values without wrap wrapWith
`
	return strings.Fields(names)
}

func TestFunctionOperationMatrixCoversHelm(t *testing.T) {
	want := helmFunctionNames()
	missing := make([]string, 0)
	for _, name := range want {
		if _, reviewed := functionOperation(name); !reviewed {
			missing = append(missing, name)
		}
	}
	if len(missing) > 0 {
		t.Fatalf("Helm functions without a reviewed formal operation: %q", missing)
	}
	if got := len(FormalFunctionOperations()); got != len(want) {
		t.Errorf("formal function rows = %d, want %d", got, len(want))
	}

	for _, name := range reviewedFunctionNames() {
		if _, exists := slices.BinarySearch(want, name); !exists {
			t.Errorf("reviewed function %q is absent from Helm 4.2.4", name)
		}
	}

	classesByName := make(map[string][]functionOperationClass)
	for _, group := range functionOperationGroups {
		for name := range group.functions {
			classesByName[name] = append(classesByName[name], group.class)
		}
	}
	for name, classes := range classesByName {
		if len(classes) != 1 {
			t.Errorf("function %q has %d formal classes: %v", name, len(classes), classes)
		}
	}
}
