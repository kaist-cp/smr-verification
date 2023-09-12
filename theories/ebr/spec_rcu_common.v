From smr.lang Require Import notation.
From iris.prelude Require Import options.

Record rcu_code : Type := RCUCode {
  rcu_domain_new : val;
  rcu_domain_retire : val;
  rcu_domain_do_reclamation : val;
  guard_new : val;
  guard_activate : val;
  guard_deactivate : val;
  guard_drop : val;
}.
