{{- define "basic.image" -}}
{{- printf "%s:%s" .repository .tag -}}
{{- end -}}

{{- define "basic.unused" -}}
{{- .Values.unusedSetting -}}
{{- end -}}
