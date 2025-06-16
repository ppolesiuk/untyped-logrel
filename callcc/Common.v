Require Source.
Require Target.
Require Import Relation_Operators.

Module S := Source.
Module T := Target.

Coercion S.e_value : S.value >-> S.expr.
Coercion S.p_expr  : S.expr >-> S.program.
