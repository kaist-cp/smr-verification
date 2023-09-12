From stdpp Require Export namespaces.
From iris.base_logic.lib Require Export iprop.
From smr.lang Require Import notation.
From smr Require Export type.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

Record alloc := Allocation {
    addr: blk;
    len: nat;
}.

Definition DomainT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (d : loc), iProp Σ.

(* NOTE: The [γ_p : gname] is overloaded with [i_p : positive] of the "base" spec. *)

(* SMR manages each memory "block", not individual addresses. User should
provide the address with 0 offset. *)
Definition ManagedT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (p : blk) (γ_p : gname) (size_p : nat) (R : resource Σ), iProp Σ.

Definition NodeInfoT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (p : blk) (γ_p : positive) (size_p : nat) (R : resource Σ), iProp Σ.

(* subnamespace for management *)
Definition mgmtN (N : namespace) := N .@ "mgmt".
(* subnamespace for storing resources *)
Definition ptrsN (N : namespace) := N .@ "ptr".
Definition ptrN (N : namespace) (p : blk) := ptrsN N .@ p.

(* DS operations has implementation mask [↑dsN ∪ (ptrsN N)]. Teach [solve_ndisj]
how to cope with union + difference.  *)
Global Hint Extern 10 (_ ⊆ _ ∖ (_ ∪ _)) => rewrite <-(difference_difference_l_L (C:=coPset)) : ndisj.
