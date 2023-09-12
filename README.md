# Modular Verification of Safe Memory Reclamation in Concurrent Separation Logic

This repository contains the proofs of the paper "Modular Verification of Safe Memory Reclamation in Concurrent Separation Logic" (OOPSLA'23) mechanized in Coq with the Iris separation logic framework.

## Build
This version is known to compile with
Coq 8.17.1 and
development versions of [Iris](https://gitlab.mpi-sws.org/iris/iris) and [Diaframe][]
as specified in [smr-verification.opam](smr-verification.opam).

The easiest way to correctly install the dependencies is [opam](https://opam.ocaml.org/doc/Install.html) (2.0 or newer).
Once you have installed opam, run:

```sh
opam switch create \
  --no-install \
  --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
  . ocaml-base-compiler.4.14.1
opam pin add -n -y coq 8.17.1

make builddep
# hit "y" for all prompts, if any
```

Finally, run `make -jN` (where `N` is the number of your CPU cores) to build the project.
The entire process (including installing dependencies) takes about 30 minutes on usual desktop machine.

Some proofs in theories/diaframe/examples may raise warning like this:
```
Too many intro patterns were supplied!
Dropping the following intro patterns:   γ_h1 n1
Too many IPM names were supplied!
Please remove "Info_h1", "M_h1", "Nodes", 
Subgoal 2 naming problems:
Too little intro patterns were supplied! Please supply a name for:
  x0 : bool
```
These are not errors.
If there were an actual error (e.g. failure to check the proof),
there will be an explicit error message starting with Error:.

If something else doesn't work, run `eval $(opam env)` and retry.

### Updating Dependencies
If the development fails to compile after pulling an update to this repository, run:

```sh
opam update && make builddep && make clean
```

and build it again with `make -jN`.

### Statistics
To obtain the line count used in Table 1, run:
```sh
python3 count_lines.py
```

and statistics will be saved in [`line_count.tsv`](line_count.tsv) (tab separated values).

## [Hazard Pointers](theories/hazptr) (§3,§4,§5)
* [`code_hazptr.v`](theories/hazptr/code_hazptr.v): implementation of hazard pointers (Fig. 2).
* [`spec_hazptr.v`](theories/hazptr/spec_hazptr.v): specifications of hazard pointers. (Fig. 5,10, and Appendix A).

  | Paper                           | Coq                          |
  |---------------------------------|------------------------------|
  | HPInv                           | `IsHazardDomainT`            |
  | Managed                         | `ManagedT`                   |
  | HPSlot & Protected              | `ShieldT`                    |
  | Managed-New{,-Full}             | `hazard_domain_register'`    |
  | Managed-Access                  | `managed_acecss'`            |
  | Protect{,-Fixed}                | `shield_protect_spec'`       |
  | Protected-Access{,-Full}        | `shield_acc'`                |
  | Unprotect                       | `shield_unset_spec'`         |
  | HPSlot-Set                      | `shield_set_spec'`           |
  | HPSlot-Validate{,-Full}         | `shield_validate'`           |
  | HP-Retire                       | `hazard_domain_retire_spec'` |
  | Protected-Managed-Agree{,-Full} | `shield_managed_agree'`      |

  * Difference between paper and code.
    * In the paper, the register rule requires a user to prove a fancy update given a fresh ID. In Coq, we simplify this process by allowing the user to pick its own ID. This allows the user to create the block resource predicate independently of the register rule, simplifying the proofs.
    * `Shield` with `Validated` `shield_state` corresponds to Protected, and the other states (`Deactivated`, `NotValidated`) correspond to HPSlot.
    * Managed-New{,-Full} vs. `hazard_domain_register'`
      * `hazard_domain_register'` has additional premise `†p…(length lv)`.
        This originates from [λRust][]'s program logic (see below) where it enforces that a `free()` call is passed the correct size of the memory block.
        We also use it to make `hazard_domain_register'` depend only on the global invariant of hazard pointers (but not the invariant of each pointer's block resource).
      * `hazard_domain_register'` does not use unique block ID provided by the hazard pointers,
        but instead it just takes a user-provided ID.
        This is fine for hazard pointers as long as the users themselves manage the IDs.
    * Protected-Access{-Full} is a Hoare triple in paper, but it is actually an access rule with "fancy update" (`={E1,E2}=∗`) in Coq. In Iris, predicate proving the access rule can be used in Hoare triples in the style presented in the paper. Proving the rule in the update form allows us to use it in contexts outside of Hoare triples (e.g, when proving another access rule), hence we prove this stronger rule.
  * Rules omitted from the paper.
    * `hazard_domain_new_spec'` is a Hoare triple for initializing hazard pointers library.
    * `shield_new_spec'` and `shield_drop_spec'` are Hoare triples for making a new HPSlot and destructing it, respectively.
    * `managed_exclusive'` rule shows uniqueness of managed pointers. It is used when we show that a pointer is not being inserted into a data structure twice, notably in the elimination stack.
    * `managed_acc` rule is Protect-Access, but for managed pointers.
    * `hazard_domain_do_reclamation_spec'` is a Hoare triple for trying to free each retired node. The only specification is that it is safe to call this at any time (there are no preconditions or postconditions).

* [`proof_hazptr.v`](theories/hazptr/proof_hazptr.v): model of predicates proof of the full hazard pointer specs.
  * The Coq formalization does not include the proof for the simplified spec (Fig. 9).
* Data structures using hazard pointers
  * `spec_*.v`: specifications of counter, stack, queue, set, and deque using Hazard pointers.
  * [`code_counter.v`](theories/hazptr/code_counter.v), [`proof_counter.v`](theories/hazptr/proof_counter.v): a simple CAS-based counter.
  * [`code_hybrid_counter.v`](theories/hazptr/code_hybrid_counter.v), [`proof_hybrid_counter.v`](theories/hazptr/proof_hybrid_counter.v): a contrived counter; a minimal example of shared mutable memory blocks.
  * [`code_treiber.v`](theories/hazptr/code_treiber.v), [`proof_treiber.v`](theories/hazptr/proof_treiber.v): Treiber stack.
  * [`code_elimstack.v`](theories/hazptr/code_elimstack.v), [`spec_stack.v`](theories/hazptr/spec_stack.v), [`proof_elimstacr.v`](theories/hazptr/proof_elimstack.v): Elimination stack.
  * [`code_ms.v`](theories/hazptr/code_ms.v), [`proof_ms.v`](theories/hazptr/proof_ms.v): Michael-Scott queue.
  * [`code_dglm.v`](theories/hazptr/code_ms.v), [`proof_dglm.v`](theories/hazptr/proof_ms.v): DGLM queue.
  * [`code_harris_michael_find.v`](theories/hazptr/code_harris_michael_find.v), [`proof_harris_michael_find.v`](theories/hazptr/proof_harris_michael_find.v): Harris-Michael's list based set's find operation.
    * We don't have Harris's set here as HP cannot be applied to Harris set in a lock-free manner.
    * The proof of set operations and initializer are in [`code_harris_operations.v`](theories/hazptr/code_harris_operations.v) and [`proof_harris_operations.v`](theories/hazptr/proof_harris_operations.v)
  * [`code_cldeque.v`](theories/hazptr/code_cldeque.v), [`proof_cldeque.v`](theories/hazptr/proof_cldeque.v): Chase-Lev deque.

* [`closed_proofs.v`](theories/hazptr/closed_proofs.v): closed proofs showing that the implementation satisfies the specifications.
* [`client.v`](theories/hazptr/client.v): example client codes using the specs of the data structures shown above, and the proof of their safety.

## [Epoch-Based RCU](theories/ebr) (§6)
* [`code_ebr.v`](theories/ebr/code_ebr.v): implementation of epoch-based RCU.
* [`spec_rcu_simple.v`](theories/ebr/spec_rcu_simple.v): a "simple" specification of RCU, very similar to `spec_hazptr.v`. However, this spec does not support optimistic traversals.
* [`spec_rcu_base.v`](theoreis/ebr/spec_rcu_base.v): base specification of RCU. (Fig. 11)

    | Paper               | Coq                       |
    | ------------------- | ------------------------- |
    | RCUState            | `RCUAuthT`                |
    | RCUSlot             | `BaseInactiveT`           |
    | Guard               | `BaseGuardT`              |
    | BlockInfo           | `BaseNodeInfoT`           |
    | RCU-Lock            | `guard_activate_spec'`    |
    | RCU-Unlock          | `guard_deactivate_spec'`  |
    | Guard-Managed-Agree | `guard_managed_agree'`    |
    | Managed-Protected   | `guard_protect'`          |
    | Managed-BlockInfo   | `managed_get_node_info'`  |
    | Guard-Access        | `guard_acc'`              |
    | RCU-Retire          | `rcu_domain_retire_spec'` |
  * Difference between paper and code.
    * In Paper, RCUState is a single map containing the status of each block ID. In Coq, we split the role into one map and one set to simplify the proof.
      * As a consequence, BlockStatus only exists in the paper. The role is split into a map and a set.
    * In Paper, Guard only has the "retired" set (Syn in Coq). In Coq, we hold the additional "guarded" map.
      * The map essentially holds the BlockInfo of all the pointers the guard has seen so far, similar to the `Validated` state of hazard pointer shields. This allows the agree rule to be a wand, as otherwise it would need to be a fancy update so that the user can open the RCU invariant to obtain the BlockInfo.
      * This additionally allows more separation-logic style rules as specs, at it is difficult to represent ''a element is **not** in a set'' with resources. Notably, we have the `BaseGuardedNodeInfo` resource, which is evidence that a block ID is not in the retired set + BlockInfo, hence most rules require it as a precondition instead.
    * `guard_activate_spec'` is not LAT in Coq, but a regular Hoare triple. This is because the synchronized set is technically a subset of the retired set at the time of activation. One can use `rcu_auth_guard_subset` to obtain this fact.
    * Rest is similar to the counterparts in hazard pointers.
  * Rules omitted from the paper.
    * `rcu_domain_register'` is like Managed-New-Full, but it also
      * registers the pointer to `RCUAuth`, and
      * allows user to produce the some extra resource `Ms i_p` during the proof of the block resource,
        which is returned to the user.
    * `rcu_auth_guard_subset` asserts that the set of ids that a guard is synchronized with must be retired. As a corollary, if a node is not yet retired, it is not synchronized with any guards.
    * `guard_protect_node_info'`: This rule is a variant of `guard_protect'`, but uses `BaseNodeInfo` and the condition that `i ∉ Syn`. It is used to protect a pointer when a guard sees a new pointer that may have been retired, but not at the time it was created. Notably, this rule is essential in proving optimistic traversals.
* [`spec_rcu_traversal.v`](theoreis/ebr/spec_rcu_base.v): traversal specification of RCU. (Fig. 12)

    | Paper                     | Coq                            |
    | ------------------------- | ------------------------------ |
    | Managed                   | `ManagedT`                     |
    | Deleted                   | `DeletedT`                     |
    | RCUPointsTo               | `RCUPointsToT`                 |
    | Guard-Protect-RCUPointsTo | `guard_protect_rcu_points_to'` |
    | RCUPointsTo-Update        | `rcu_points_to_update'`        |
    | Managed-Delete            | `managed_delete'`              |
    | Deleted-Retire            | `deleted_retire'`              |
  * Difference between paper and code.
    * In paper, Guard has a detached set. In Coq, we hide this behind an existential and instead utilize the `BaseGuardedNodeInfo` from the base spec to prove protection. This allows the client to not need to prove any pure facts, which can get annoying when Coq infers the wrong evars.
  * Rules omitted from the paper.
    * `rcu_points_to_link'`, `rcu_points_to_unlink` and `deleted_clean'` are variants of `rcu_points_to_update'` that allow for more robust proofs when managing links.
    * `rcu_domain_register` accepts the (1) physical resources of the pointer, the (2) list of pointers to point to, (3) fancy update to create a block resource, and creates a new Managed that points to the given list.
      * The rule seems overly complex, but it is necessary to ensure that the related invariants can be properly opened.
    * The predicates in the traversal spec also admit access rules similar to hazard pointers and the rcu base spec.

* [`proof_ebr_rcu_base.v`](theories/ebr/proof_ebr_rcu_base.v): proof that the ebr code satisfies the base RCU spec.
* [`proof_rcu_simple.v`](theories/ebr/proof_rcu_simple.v): proof that the base RCU spec, along with a bit of ghost state, satisfies the simple RCU spec.
* [`proof_rcu_traversal.v`](theories/ebr/proof_rcu_simple.v): proof that the base RCU spec, along with the node link history ghost and a bit of ghost state, satisfies the traversal RCU spec.
* Data structures using epoch-based RCU
  * `spec_*.v`: specifications of counter, stack, queue, set, and deque using RCU.
  * [`code_harris_find.v`](theories/ebr/code_harris_michael_find.v), [`proof_harris_find.v`](theories/ebr/proof_harris_michael_find.v): Harris set's find operation.
    * Proof of Harris's list based set showcases proof of optimistic traversal.
    * The proof of set operations and initializer are in [`code_harris_operations.v`](theories/ebr/code_harris_operations.v) and [`proof_harris_operations.v`](theories/hazptr/proof_harris_operations.v)
  * Other examples are analogous to that of hazard pointers.

* [`closed_proofs.v`](theories/ebr/closed_proofs.v): closed proofs showing that the implementation satisfies the specifications.
    In particular, the proofs of the traversal and simple specs are instantiated using the proof of the base spec.
* [`client.v`](theories/ebr/client.v): example client codes using the specs of the data structures shown above, and the proof of their safety.

## [`diaframe`](theories/diaframe)
Experimentation for applying [Diaframe][], a separation logic automation framework, to our specification.

The interesting files are as follows.
* [hints/hazptr_hints](theories/diaframe/hints/hazptr_hints.v): automation hints for using the hazptr specs.
* [hints/rcu_hints](theories/diaframe/hints/rcu_hints.v): automation hints for using the RCU specs.
* [hints/ghost_var](theories/diaframe/hints/ghost_var_hints.v): automation hints for ghost var used in Treiber's stack.
* [examples/proof_treiber_no_recl.v](examples/proof_treiber_no_recl.v): An automation of `theories/no_recl/proof_treiber.v`.
* [examples/proof_treiber_hazptr.v](examples/proof_treiber_hazptr.v): An automation of `theories/hazptr/proof_treiber.v`.
* [examples/proof_treiber_rcu.v](examples/proof_treiber_rcu.v): An automation of `theories/ebr/proof_treiber.v`.

## Other Files

### [`no_recl`](theories/no_recl)
* Code, specification, and proof of DSs without reclamation.
* Used as a starting point of proofs of DSs with reclamation and overhead comparison as shown in Table 1.

### [`theories`](theories)
* [`code_retired_list.v`](theories/code_retired_list.v), [`spec_retired_list.v`](theories/spec_retired_list.v), [`proof_retired_list.v`](theories/proof_retired_list.v): retired node list, used in the implementation of hazard pointers.
* [`code_slot_bag_oloc.v`](theories/code_slot_bag_oloc.v), [`spec_slot_bag_oloc.v`](theories/spec_slot_bag_oloc.v), [`proof_slot_bag_oloc.v`](theories/proof_slot_bag_oloc.v), [`code_slot_bag_onat.v`](theories/code_slot_bag_onat.v), [`spec_slot_bag_onat.v`](theories/spec_slot_bag_onat.v), [`proof_slot_bag_onat.v`](theories/proof_slot_bag_onat.v): slot list, used in the implementation of hazard pointers (slots containing `option loc`) and epoch-based RCU (slots containing `option nat`).
  They use slot list instead of fixed array in order to support dynamic registration.
  Slot list specification provides `Slot` predicate, which behaves similarly to the half points-to.
* [`helpers.v`](theories/helpers.v): helper lemmas.
* [`sorted_list.v`](theories/sorted_list.v): helper lemmas for sorted list, used in the proofs of Harris{,-Michael}'s list.
* [`smr_common.v`](theories/smr_common.v): domain & managed types and namespaces.
* [`type.v`](theories/type.v): recursive types to represent block info for RCU traversal specification, adapted from λRust.

### [`lang`](theories/lang)
We use a toy language that supports prophecy and allocator that reuses freed locations.
The implementation is based on [HeapLang](https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris_heap_lang) and [λRust][].

### [`program_logic`](theories/program_logic)
This directory contains a single file, [`atomic.v`](theories/program_logic/atomic.v): a modified version of Iris' [`atomic.v`](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/program_logic/atomic.v). Specifically, we need non-empty inner masks for LATs because SMR rules need their internal invariants.

### [`logic`](theories/logic)
* [`epoch_history.v`](theories/logic/epoch_history.v): The list of unlinked pointers made at each epoch, used to verify the Epoch-Based RCU.
* [`node_link_history.v`](theories/logic/node_link_history.v): The history of node events, used to prove the soundness RCU with optimistic traversal.
* [`reclamation.v`](theories/logic/reclamation.v): Intermediate resources and associated rules common to the proofs of hazard pointer and RCU specifications.
* [`token2.v`](theories/logic/token2.v): An RA of two-dimensional tokens, used in `reclamation.v`.

### [`algebra`](theories/algebra)
In `algebra` and [`base_logic`](theories/base_logic/lib), we use several variants of existing RAs replacing positive rational numbers with coPsets(co-finite positive integer sets). This is for a more fine-grained control of fractional resources: e.g. to distribute fractions to unbounded number of managed pointers and store the remaining fraction into the domain.

* [`gset.v`](theories/algebra/gset.v): Non-empty gsets and their RA with disjoint union.
* [`coPset.v`](theories/algebra/coPset.v): Non-empty coPsets and their RA with disjoint union.
* [`coP_auth.v`](theories/algebra/coP_auth.v): The fractional auth RA, but using non-empty coPsets for fractional tokens instead of positive rational numbers.
* [`coP_gmap_view.v`](theories/algebra/coP_gmap_view.v): The gmap view RA, but using non-empty coPsets for fractional tokens instead of positive rational numbers.

### [`base_logic/lib`](theories/base_logic/lib)
* [`coP_cancellable_invariants.v`](theories/base_logic/lib/coP_cancellable_invariants.v): Cancellable invariants, but using non-empty coPsets for fractional tokens instead of positive rational numbers.
* [`coP_ghost_map.v`](theories/base_logic/lib/coP_ghost_map.v): Ghost maps, but using non-empty coPsets for fractional tokens instead of positive rational numbers.
* [`ghost_vars.v`](theories/base_logic/lib/ghost_vars.v): The ghost state mapping each positive integer, and each pair of positive integers, to a ghost variable.
* [`mono_list.v`](theories/base_logic/lib/mono_list.v): The ghost state of monotonically growing lists, [taken from the nightly version of Iris](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_staging/base_logic/mono_list.v).
* [`mono_nats.v`](theories/base_logic/lib/mono_nats.v): The ghost state of monotonically growing natural numbers, [taken from Iris](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/mono_nat.v), modified to support fixing the number to a persistent value.
* [`mono_nats.v`](theories/base_logic/lib/mono_nats.v): The ghost state mapping each positive integer to [`mono_nat`](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/mono_nat.v), monotonically increasing natural numbers.


[Diaframe]: https://gitlab.mpi-sws.org/iris/diaframe
[λRust]: https://gitlab.mpi-sws.org/iris/lambda-rust
