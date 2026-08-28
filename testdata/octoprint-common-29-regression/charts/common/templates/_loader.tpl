{{- define "common.loader.all" -}}
apiVersion: v1
kind: ConfigMap
metadata:
  name: services
data:
  checksum: {{ .Values.service | toJson | sha256sum | quote }}
{{- if .Values.service.main.ports.main }}
{{- range $serviceName, $service := .Values.service }}
  {{- if $service.enabled }}
    {{- range $portName, $port := $service.ports }}
      {{- if $port.enabled }}
  {{ printf "%s-%s" $serviceName $portName }}: {{ printf "%v:%v" $port.port $port.targetPort | quote }}
      {{- end }}
    {{- end }}
  {{- end }}
{{- end }}
{{- end }}
{{- end }}
