Require Import List.
Require Import String.

Notation "'for' 'each' e 'of' l , p" :=
  (List.Forall (fun e => p) l)
    (at level 200, e ident, right associativity).

Notation "'values' e 'for' x 'of' f 'are' 'distinct'" :=
  (forall x, List.count_occ string_dec (List.map (fun x => e) f) x <= 1)
    (at level 200, x ident).
