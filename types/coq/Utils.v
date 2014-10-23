Require Import List.
Require Import String.

Notation "'for' 'each' e 'of' l , p" :=
  (List.Forall (fun e => p) l)
    (at level 200, e ident, right associativity).

Notation "'values' e 'for' x 'of' f 'are' 'distinct'" :=
  (List.NoDup (List.map (fun x => e) f))
    (at level 200, x ident).

Notation "'for' 'each' e f 'of' l m , p" :=
  (List.Forall2 (fun e f => p) l m)
    (at level 200, e ident, f ident, right associativity, l at level 1, m at level 1).
