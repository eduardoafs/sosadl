#!/bin/sh

echo -n 'rules count: '

grep -E '\|[[:space:]]+(type_|mode_|First_Field|Next_Field|subtype_|incrementally_|simple_increment_|mutually_|optionally_|constexpr_|check_|range_modulo_|smallest_|greatest_|condition_)' SosADL/TypeSystem.v | wc -l

echo -n 'judgements count: '
grep -E '^[[:space:]]*(Inductive|with)[[:space:]]+(type_|mode_|field_has_type|subtype|optionally|constexpr_|check_datatype|range_modulo_|smallest|greatest|condition_)' SosADL/TypeSystem.v | wc -l
