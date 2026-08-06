import Mathlib
import Lax41.HaeuplerSahaSrinivasanTheorem22
import Lax41Proofs.MoserTardos

set_option autoImplicit false

open scoped ENNReal

namespace Lax41Proofs

open Lax41.MoserTardosDefinitions
open Lax41.HaeuplerSahaSrinivasanDefinitions

variable {E : Type} [Fintype E] [DecidableEq E]

/-! ## A root used only once -/

/--
The weight of a bounded witness tree whose distinguished root has weight
`rootWeight`, while every proper descendant is weighted by `p`.
-/
noncomputable def BTree.queryWeight (r : E → E → Prop) [DecidableRel r]
    (rootWeight : ℝ≥0∞) (p : E → ℝ≥0∞) {n : Nat} {root : E}
    (t : BTree E (n + 1) root) : ℝ≥0∞ :=
  rootWeight * ∏ b : E, match t b with
    | none => 1
    | some u => if r root b then u.weight r p else 0

theorem BTree.sum_queryWeight (r : E → E → Prop) [DecidableRel r]
    (rootWeight : ℝ≥0∞) (p : E → ℝ≥0∞) (n : Nat) (root : E) :
    (∑ t : BTree E (n + 1) root, t.queryWeight r rootWeight p) =
      rootWeight * ∏ b : E,
        (1 + if r root b then ∑ u : BTree E n b, u.weight r p else 0) := by
  classical
  simp only [BTree.queryWeight, BTree]
  rw [← Finset.mul_sum]
  congr 1
  rw [show (∏ b : E,
      (1 + if r root b then ∑ u : BTree E n b, u.weight r p else 0)) =
      ∏ b : E, ∑ o : Option (BTree E n b),
        match o with
        | none => 1
        | some u => if r root b then u.weight r p else 0 by
    congr with b
    simp]
  exact (Fintype.prod_sum (fun b (o : Option (BTree E n b)) =>
    match o with
    | none => 1
    | some u => if r root b then u.weight r p else 0)).symm

theorem BTree.sum_queryWeight_le_of_charge (r : E → E → Prop) [DecidableRel r]
    (rootWeight : ℝ≥0∞) (p y : E → ℝ≥0∞)
    (hcharge : ∀ a, p a * ∏ b : E,
      (if r a b then 1 + y b else 1) ≤ y a)
    (n : Nat) (root : E) :
    (∑ t : BTree E (n + 1) root, t.queryWeight r rootWeight p) ≤
      rootWeight * ∏ b : E, (if r root b then 1 + y b else 1) := by
  rw [BTree.sum_queryWeight]
  gcongr with b
  by_cases hr : r root b
  · simp only [hr, if_pos]
    simpa [add_comm] using
      add_le_add_left (BTree.sum_weight_le_of_charge r p y hcharge n b) 1
  · simp [hr]

/-- The corresponding path-product description of `BTree.queryWeight`. -/
noncomputable def BTree.queryPathWeight (rootWeight : ℝ≥0∞)
    (p : E → ℝ≥0∞) (root : E) {n : Nat} {a : E}
    (t : BTree E n a) : ℝ≥0∞ :=
  rootWeight * ∏ q ∈ t.paths.erase [], p (pathLabel root q)

theorem BTree.queryPathWeight_succ (rootWeight : ℝ≥0∞)
    (p : E → ℝ≥0∞) (n : Nat) (root : E) (t : BTree E (n + 1) root) :
    t.queryPathWeight rootWeight p root =
      rootWeight * ∏ b : E, match t b with
        | none => 1
        | some u => u.pathWeight p b := by
  classical
  rw [BTree.queryPathWeight, BTree.paths_eq_insert_biUnion,
    Finset.erase_insert (by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      push Not
      exact fun b ↦ t.nil_not_mem_childBlock)]
  congr 1
  rw [Finset.prod_biUnion t.childBlock_pairwiseDisjoint]
  apply Finset.prod_congr rfl
  intro b _hb
  cases htb : t b with
  | none => simp [BTree.childBlock, htb]
  | some u =>
      rw [show t.childBlock b = u.paths.image (b :: ·) by
        simp [BTree.childBlock, htb], Finset.prod_image]
      · rfl
      · intro q _hq q' _hq' heq
        exact List.cons.inj heq |>.2

theorem BTree.queryWeight_eq_queryPathWeight (r : E → E → Prop)
    [DecidableRel r] (rootWeight : ℝ≥0∞) (p : E → ℝ≥0∞)
    (n : Nat) (root : E) (t : BTree E (n + 1) root)
    (hvalid : t.EdgeValid r root) :
    t.queryWeight r rootWeight p = t.queryPathWeight rootWeight p root := by
  rw [BTree.queryWeight, BTree.queryPathWeight_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro b _hb
  cases htb : t b with
  | none => simp
  | some u =>
      have hr : r root b := BTree.root_related_of_child htb hvalid
      simp only [hr, if_pos]
      exact BTree.weight_eq_pathWeight_of_edgeValid r p u
        (BTree.child_edgeValid htb hvalid)

/-- Root weight times the product of the weights of all non-root nodes. -/
noncomputable def ProperTree.queryWeight {r : E → E → Prop} {root : E}
    (rootWeight : ℝ≥0∞) (p : E → ℝ≥0∞) (t : ProperTree r root) : ℝ≥0∞ :=
  rootWeight * ∏ q ∈ t.paths.erase [], p (pathLabel root q)

theorem ProperTree.toBTree_queryWeight (r : E → E → Prop) [DecidableRel r]
    {root : E} (rootWeight : ℝ≥0∞) (p : E → ℝ≥0∞)
    (t : ProperTree r root) (n : Nat)
    (hdepth : ∀ q ∈ t.paths, q.length < n + 1) :
    (t.toBTree n hdepth).queryWeight r rootWeight p =
      t.queryWeight rootWeight p := by
  rw [BTree.queryWeight_eq_queryPathWeight r rootWeight p n root _
    (t.toBTree_edgeValid n hdepth), BTree.queryPathWeight,
    ProperTree.queryWeight, t.toBTree_paths n hdepth]

/--
The branching-process estimate when the root is an observed event that is not
allowed to occur below the root.
-/
theorem ProperTree.tsum_queryWeight_le_of_charge
    (r : E → E → Prop) [DecidableRel r]
    (rootWeight : ℝ≥0∞) (p y : E → ℝ≥0∞)
    (hcharge : ∀ a, p a * ∏ b : E,
      (if r a b then 1 + y b else 1) ≤ y a)
    (root : E) (valid : ProperTree r root → Prop) :
    (∑' t : {t : ProperTree r root // valid t},
      t.1.queryWeight rootWeight p) ≤
      rootWeight * ∏ b : E, (if r root b then 1 + y b else 1) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S ↦ ?_
  let n := S.sup fun t ↦ t.1.paths.sup List.length
  have hdepth (t : {t : ProperTree r root // valid t})
      (ht : t ∈ S) : ∀ q ∈ t.1.paths, q.length < n + 1 := by
    intro q hq
    apply Nat.lt_succ_of_le
    exact (Finset.le_sup (f := List.length) hq).trans
      (Finset.le_sup
        (f := fun t : {t : ProperTree r root // valid t} ↦
          t.1.paths.sup List.length) ht)
  let encode (t : {t : ProperTree r root // valid t}) :
      BTree E (n + 1) root :=
    if ht : t ∈ S then t.1.toBTree n (hdepth t ht) else fun _ ↦ none
  have hencode_inj : Set.InjOn encode
      (↑S : Set {t : ProperTree r root // valid t}) := by
    intro s hs t ht heq
    change s ∈ S at hs
    change t ∈ S at ht
    apply Subtype.ext
    apply ProperTree.ext
    rw [show encode s = s.1.toBTree n (hdepth s hs) by simp [encode, hs],
      show encode t = t.1.toBTree n (hdepth t ht) by simp [encode, ht]] at heq
    rw [← s.1.toBTree_paths n (hdepth s hs),
      ← t.1.toBTree_paths n (hdepth t ht), heq]
  calc
    ∑ t ∈ S, t.1.queryWeight rootWeight p =
        ∑ t ∈ S, (encode t).queryWeight r rootWeight p := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [show encode t = t.1.toBTree n (hdepth t ht) by simp [encode, ht]]
      exact (t.1.toBTree_queryWeight r rootWeight p n (hdepth t ht)).symm
    _ = ∑ u ∈ S.image encode, u.queryWeight r rootWeight p := by
      rw [Finset.sum_image hencode_inj]
    _ ≤ ∑ u : BTree E (n + 1) root, u.queryWeight r rootWeight p := by
      apply Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ rootWeight * ∏ b : E, (if r root b then 1 + y b else 1) :=
      BTree.sum_queryWeight_le_of_charge r rootWeight p y hcharge n root

/-! ## Adding an observed event to the execution -/

section ObservedEvent

variable {I : Type} [Fintype I] [DecidableEq I]
variable (Value : I → Type) [∀ i, MeasurableSpace (Value i)]

/-- The observed event is the `none` label; algorithmic bad events are `some e`. -/
def observedScope (scope : E → Finset I) (queryScope : Finset I) :
    Option E → Finset I
  | none => queryScope
  | some e => scope e

/-- The event family obtained by adjoining the observed event as `none`. -/
def observedEvent (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope)) :
    ∀ label, Set (LocalAssignment Value (observedScope scope queryScope label))
  | none => query
  | some e => bad e

/-- The observed event is true in a complete assignment. -/
def queryHolds (queryScope : Finset I)
    (query : Set (LocalAssignment Value queryScope))
    (assignment : Assignment Value) : Prop :=
  (fun i : queryScope ↦ assignment i.1) ∈ query

theorem measurableSet_queryHolds (queryScope : Finset I)
    (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query) :
    MeasurableSet {assignment : Assignment Value |
      queryHolds Value queryScope query assignment} := by
  apply hquery.preimage
  change Measurable (fun (assignment : Assignment Value) (i : queryScope) ↦
    assignment i.1)
  fun_prop

/-- The rule that gives the observed event priority over the original rule. -/
noncomputable def observedChoose (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (assignment : Assignment Value) : Option (Option E) := by
  classical
  exact if queryHolds Value queryScope query assignment then some none
    else (rule.choose assignment).map some

/-- A resampling rule on the enlarged family, prioritizing the observed event. -/
noncomputable def observedRule (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query) :
    ResamplingRule Value (observedScope scope queryScope)
      (observedEvent Value scope bad queryScope query) where
  choose := observedChoose Value scope bad rule queryScope query
  measurable_fiber := by
    intro result
    have hq := measurableSet_queryHolds Value queryScope query hquery
    cases result with
    | none =>
        rw [show {assignment |
            observedChoose Value scope bad rule queryScope query assignment = none} =
            {assignment | ¬queryHolds Value queryScope query assignment} ∩
              {assignment | rule.choose assignment = none} by
          ext assignment
          by_cases hqa : queryHolds Value queryScope query assignment
          · simp [observedChoose, hqa]
          · cases hchoice : rule.choose assignment <;>
              simp [observedChoose, hqa, hchoice]]
        exact hq.compl.inter (rule.measurable_fiber none)
    | some label =>
        cases label with
        | none =>
            rw [show {assignment |
                observedChoose Value scope bad rule queryScope query assignment = some none} =
                {assignment | queryHolds Value queryScope query assignment} by
              ext assignment
              simp [observedChoose]]
            exact hq
        | some e =>
            rw [show {assignment |
                observedChoose Value scope bad rule queryScope query assignment = some (some e)} =
                {assignment | ¬queryHolds Value queryScope query assignment} ∩
                  {assignment | rule.choose assignment = some e} by
              ext assignment
              by_cases hqa : queryHolds Value queryScope query assignment
              · simp [observedChoose, hqa]
              · cases hchoice : rule.choose assignment <;>
                  simp [observedChoose, hqa, hchoice]]
            exact hq.compl.inter (rule.measurable_fiber (some e))
  sound := by
    intro assignment label hchoose
    cases label with
    | none =>
        have hq : queryHolds Value queryScope query assignment := by
          by_contra hnq
          simp [observedChoose, hnq] at hchoose
        simpa [violates, restrictAssignment, observedScope, observedEvent,
          queryHolds] using hq
    | some e =>
        have hnq : ¬queryHolds Value queryScope query assignment := by
          intro hq
          simp [observedChoose, hq] at hchoose
        have he : rule.choose assignment = some e := by
          simpa [observedChoose, hnq] using hchoose
        simpa [violates, restrictAssignment, observedScope, observedEvent] using
          rule.sound he
  complete := by
    intro assignment hchoose
    have hnq : ¬queryHolds Value queryScope query assignment := by
      intro hq
      simp [observedChoose, hq] at hchoose
    have hnone : rule.choose assignment = none := by
      simpa [observedChoose, hnq] using hchoose
    intro label
    cases label with
    | none =>
        simpa [violates, restrictAssignment, observedScope, observedEvent,
          queryHolds] using hnq
    | some e =>
        simpa [violates, restrictAssignment, observedScope, observedEvent] using
          rule.complete hnone e

/-- The observed event holds at stage `n` of the original execution. -/
def queryOccursAt (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (n : Nat) : Prop :=
  queryHolds Value queryScope query
    (currentAssignment Value table (runCounts Value scope bad rule table n))

theorem advanceCounts_observed_map (scope : E → Finset I)
    (queryScope : Finset I) (counts : I → Nat) (selected : Option E) :
    advanceCounts (observedScope scope queryScope) counts (selected.map some) =
      advanceCounts scope counts selected := by
  cases selected <;> rfl

theorem runCounts_eq_of_log_none_of_le (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    {n m : Nat} (hnm : n ≤ m)
    (hnone : resamplingLog Value scope bad rule table n = none) :
    runCounts Value scope bad rule table m =
      runCounts Value scope bad rule table n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, runCounts_succ]
      have hlog : resamplingLog Value scope bad rule table (n + d) = none :=
        resamplingLog_eq_none_of_le Value scope bad rule table (by omega) hnone
      simp [hlog, advanceCounts, ih]

theorem log_ne_none_before_first_query (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (t : Nat) (ht : queryOccursAt Value scope bad rule table queryScope query t)
    (hfirst : ∀ k < t,
      ¬queryOccursAt Value scope bad rule table queryScope query k)
    {k : Nat} (hk : k < t) :
    resamplingLog Value scope bad rule table k ≠ none := by
  intro hnone
  have hcounts := runCounts_eq_of_log_none_of_le Value scope bad rule table
    (Nat.le_of_lt hk) hnone
  have hquery : queryOccursAt Value scope bad rule table queryScope query k := by
    unfold queryOccursAt at *
    rw [← hcounts]
    exact ht
  exact hfirst k hk hquery

theorem observed_runCounts_eq_before_first_query (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query)
    (t : Nat) (hfirst : ∀ k < t,
      ¬queryOccursAt Value scope bad rule table queryScope query k) :
    ∀ n ≤ t,
      runCounts Value (observedScope scope queryScope)
          (observedEvent Value scope bad queryScope query)
          (observedRule Value scope bad rule queryScope query hquery) table n =
        runCounts Value scope bad rule table n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < t := by omega
      have hnle : n ≤ t := Nat.le_of_lt hnlt
      have hnot : ¬queryOccursAt Value scope bad rule table queryScope query n :=
        hfirst n hnlt
      rw [runCounts_succ, runCounts_succ, ih hnle]
      unfold resamplingLog
      rw [ih hnle]
      change advanceCounts (observedScope scope queryScope)
          (runCounts Value scope bad rule table n)
          (observedChoose Value scope bad rule queryScope query
            (currentAssignment Value table (runCounts Value scope bad rule table n))) =
        advanceCounts scope (runCounts Value scope bad rule table n)
          (rule.choose
            (currentAssignment Value table (runCounts Value scope bad rule table n)))
      have hnq : ¬queryHolds Value queryScope query
          (currentAssignment Value table (runCounts Value scope bad rule table n)) := by
        exact hnot
      rw [show observedChoose Value scope bad rule queryScope query
          (currentAssignment Value table (runCounts Value scope bad rule table n)) =
          (rule.choose
            (currentAssignment Value table (runCounts Value scope bad rule table n))).map some by
        simp [observedChoose, hnq]]
      exact advanceCounts_observed_map scope queryScope _ _

theorem observed_log_at_first_query (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query)
    (t : Nat) (ht : queryOccursAt Value scope bad rule table queryScope query t)
    (hfirst : ∀ k < t,
      ¬queryOccursAt Value scope bad rule table queryScope query k) :
    resamplingLog Value (observedScope scope queryScope)
        (observedEvent Value scope bad queryScope query)
        (observedRule Value scope bad rule queryScope query hquery) table
        t = some none := by
  rw [resamplingLog,
    observed_runCounts_eq_before_first_query Value scope bad rule table queryScope query
      hquery t hfirst _ le_rfl]
  change observedChoose Value scope bad rule queryScope query
      (currentAssignment Value table (runCounts Value scope bad rule table
        t)) = some none
  simpa [observedChoose, queryOccursAt] using ht

theorem observed_log_before_first_query (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query)
    (t : Nat) (ht : queryOccursAt Value scope bad rule table queryScope query t)
    (hfirst : ∀ k < t,
      ¬queryOccursAt Value scope bad rule table queryScope query k)
    {k : Nat} (hk : k < t) :
    ∃ e, resamplingLog Value (observedScope scope queryScope)
        (observedEvent Value scope bad queryScope query)
        (observedRule Value scope bad rule queryScope query hquery) table k =
      some (some e) := by
  have hbase := log_ne_none_before_first_query Value scope bad rule table
    queryScope query t ht hfirst hk
  obtain ⟨e, he⟩ : ∃ e, resamplingLog Value scope bad rule table k = some e := by
    cases hlog : resamplingLog Value scope bad rule table k with
    | none => exact (hbase hlog).elim
    | some e => exact ⟨e, rfl⟩
  refine ⟨e, ?_⟩
  rw [resamplingLog,
    observed_runCounts_eq_before_first_query Value scope bad rule table queryScope query
      hquery t hfirst k (Nat.le_of_lt hk)]
  change observedChoose Value scope bad rule queryScope query
      (currentAssignment Value table (runCounts Value scope bad rule table k)) =
    some (some e)
  have hnq : ¬queryOccursAt Value scope bad rule table queryScope query k :=
    hfirst k hk
  have hnq' : ¬queryHolds Value queryScope query
      (currentAssignment Value table (runCounts Value scope bad rule table k)) :=
    hnq
  simpa [observedChoose, hnq', resamplingLog] using he

/-- Probabilities on the enlarged event family. -/
def observedProbability (queryProbability : ℝ≥0∞) (p : E → ℝ≥0∞) :
    Option E → ℝ≥0∞
  | none => queryProbability
  | some e => p e

/-- Descendant weights, with the observed root and forbidden labels removed. -/
noncomputable def allowedDescendantProbability (allowed : E → Prop)
    (p : E → ℝ≥0∞) : Option E → ℝ≥0∞ := by
  classical
  intro label
  exact match label with
    | none => 0
    | some e => if allowed e then p e else 0

/-- A query witness tree has one observed root and only allowed bad labels. -/
def observedTreeValid (scope : E → Finset I) (queryScope : Finset I)
    (allowed : E → Prop)
    (t : ProperTree (scopeRelated (observedScope scope queryScope)) none) : Prop :=
  t.labelCount none = 1 ∧
    ∀ q ∈ t.paths, ∀ e, pathLabel none q = some e → allowed e

theorem ProperTree.weight_observed_eq_queryWeight
    (scope : E → Finset I) (queryScope : Finset I)
    (allowed : E → Prop) (queryProbability : ℝ≥0∞) (p : E → ℝ≥0∞)
    (t : ProperTree (scopeRelated (observedScope scope queryScope)) none)
    (hvalid : observedTreeValid scope queryScope allowed t) :
    t.weight (observedProbability queryProbability p) =
      t.queryWeight queryProbability (allowedDescendantProbability allowed p) := by
  classical
  have hfiltered : t.paths.filter (fun q ↦ pathLabel none q = none) = {[]} := by
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (by
      simpa [ProperTree.labelCount] using hvalid.1)
    have hnil : [] ∈ t.paths.filter (fun q ↦ pathLabel none q = none) := by
      simp [t.root_mem]
    rw [hq] at hnil
    have hqnil : q = [] := by simpa [eq_comm] using hnil
    simpa [hqnil] using hq
  have hroot_unique {q : List (Option E)} (hq : q ∈ t.paths)
      (hlabel : pathLabel none q = none) : q = [] := by
    have hqf : q ∈ t.paths.filter (fun z ↦ pathLabel none z = none) :=
      Finset.mem_filter.mpr ⟨hq, hlabel⟩
    rw [hfiltered] at hqf
    simpa using hqf
  have hpaths : t.paths = insert [] (t.paths.erase []) := by
    exact (Finset.insert_erase t.root_mem).symm
  rw [ProperTree.weight, ProperTree.queryWeight, hpaths,
    Finset.prod_insert (Finset.notMem_erase _ _)]
  simp only [pathLabel_nil, observedProbability]
  rw [Finset.erase_insert (Finset.notMem_erase _ _)]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  have hqpaths : q ∈ t.paths := Finset.mem_of_mem_erase hq
  have hqnil : q ≠ [] := Finset.ne_of_mem_erase hq
  cases hlabel : pathLabel none q with
  | none => exact (hqnil (hroot_unique hqpaths hlabel)).elim
  | some e =>
      have he : allowed e := hvalid.2 q hqpaths e hlabel
      simp [allowedDescendantProbability, he]

theorem occurrenceTree_observed_valid (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad) (table : ResamplingTable Value)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query) (allowed : E → Prop)
    (hallowed : ∀ (assignment : Assignment Value) (e : E),
      ¬queryHolds Value queryScope query assignment →
      rule.choose assignment = some e → allowed e)
    (t : Nat) (ht : queryOccursAt Value scope bad rule table queryScope query t)
    (hfirst : ∀ k < t,
      ¬queryOccursAt Value scope bad rule table queryScope query k) :
    observedTreeValid scope queryScope allowed
      (occurrenceTree Value (observedScope scope queryScope)
        (observedEvent Value scope bad queryScope query)
        (observedRule Value scope bad rule queryScope query hquery) table none t) := by
  classical
  let oscope := observedScope scope queryScope
  let obad := observedEvent Value scope bad queryScope query
  let orule := observedRule Value scope bad rule queryScope query hquery
  have htaug : resamplingLog Value oscope obad orule table t = some none := by
    exact observed_log_at_first_query Value scope bad rule table queryScope query
      hquery t ht hfirst
  constructor
  · rw [occurrenceTree, historyTree_root_labelCount]
    change @List.count (Option E) instBEqOfDecidableEq none
        (executionHistory Value oscope obad orule table none t) + 1 = 0 + 1
    congr 1
    apply (@List.count_eq_zero (Option E) instBEqOfDecidableEq
      (by infer_instance) none
      (executionHistory Value oscope obad orule table none t)).mpr
    intro hmem
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hklt : k < t := by simpa [executionHistory] using hk
    obtain ⟨e, hlog⟩ := observed_log_before_first_query Value scope bad rule table
      queryScope query hquery t ht hfirst hklt
    have hvalue :
        (executionHistory Value oscope obad orule table none t)[k] = some e := by
      simp [executionHistory, oscope, obad, orule, hlog]
    rw [hvalue] at hget
    simp at hget
  · intro q hq e hlabel
    let history := executionHistory Value oscope obad orule table none t
    change q ∈ (buildTimedTree (scopeRelated oscope) none history).paths at hq
    obtain ⟨k, hk⟩ := TimedTree.mem_paths.mp hq
    let good := buildTimedTree_good (scopeRelated oscope)
      (scopeRelated_refl oscope) (scopeRelated_symm oscope) none history
    rcases good.represents hk with hrep | hroot
    · have hkHistory : k < history.length := by
        by_contra hnot
        have hnone : history[k]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_gt hnot)
        rw [hrep] at hnone
        simp at hnone
      have hklt : k < t := by simpa [history, executionHistory] using hkHistory
      have hhistoryLog := executionHistory_getElem?_eq_log Value oscope obad orule
        table htaug hklt
      change history[k]? = resamplingLog Value oscope obad orule table k at hhistoryLog
      have haug : resamplingLog Value oscope obad orule table k = some (some e) := by
        rw [← hhistoryLog, hrep, hlabel]
      have hcounts := observed_runCounts_eq_before_first_query Value scope bad rule
        table queryScope query hquery t hfirst k (Nat.le_of_lt hklt)
      have hnq : ¬queryHolds Value queryScope query
          (currentAssignment Value table (runCounts Value scope bad rule table k)) :=
        hfirst k hklt
      rw [resamplingLog, hcounts] at haug
      change observedChoose Value scope bad rule queryScope query
          (currentAssignment Value table (runCounts Value scope bad rule table k)) =
        some (some e) at haug
      have hbase : rule.choose
          (currentAssignment Value table (runCounts Value scope bad rule table k)) =
          some e := by
        simpa [observedChoose, hnq] using haug
      exact hallowed _ e hnq hbase
    · have hqnil : q = [] := by simpa [history] using hroot.2
      rw [hqnil] at hlabel
      simp at hlabel

theorem queryEverOccurs_subset_iUnion_passes (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : ResamplingRule Value scope bad)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query) (allowed : E → Prop)
    (hallowed : ∀ (assignment : Assignment Value) (e : E),
      ¬queryHolds Value queryScope query assignment →
      rule.choose assignment = some e → allowed e) :
    {table | ∃ n, queryOccursAt Value scope bad rule table queryScope query n} ⊆
      ⋃ tree : {t : ProperTree
          (scopeRelated (observedScope scope queryScope)) none //
          observedTreeValid scope queryScope allowed t},
        tree.1.passes Value (observedScope scope queryScope)
          (observedEvent Value scope bad queryScope query) := by
  classical
  intro table htable
  obtain ⟨_n, hn⟩ := htable
  let first := Nat.find ⟨_n, hn⟩
  have hfirst_occurs :
      queryOccursAt Value scope bad rule table queryScope query first :=
    Nat.find_spec ⟨_n, hn⟩
  have hminimal : ∀ k < first,
      ¬queryOccursAt Value scope bad rule table queryScope query k := by
    intro k hk
    exact Nat.find_min ⟨_n, hn⟩ hk
  let tree : ProperTree (scopeRelated (observedScope scope queryScope)) none :=
    occurrenceTree Value (observedScope scope queryScope)
      (observedEvent Value scope bad queryScope query)
      (observedRule Value scope bad rule queryScope query hquery) table none first
  have hvalid : observedTreeValid scope queryScope allowed tree := by
    exact occurrenceTree_observed_valid Value scope bad rule table queryScope query
      hquery allowed hallowed first hfirst_occurs hminimal
  apply Set.mem_iUnion.mpr
  refine ⟨⟨tree, hvalid⟩, ?_⟩
  exact historyTree_passes_of_resamplingLog_eq_some Value
    (observedScope scope queryScope)
    (observedEvent Value scope bad queryScope query)
    (observedRule Value scope bad rule queryScope query hquery) table
    (observed_log_at_first_query Value scope bad rule table queryScope query
      hquery first hfirst_occurs hminimal)

theorem measure_queryEverOccurs_le_tsum_queryWeight
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : ResamplingRule Value scope bad)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query) (allowed : E → Prop)
    (hallowed : ∀ (assignment : Assignment Value) (e : E),
      ¬queryHolds Value queryScope query assignment →
      rule.choose assignment = some e → allowed e) :
    tableMeasure Value distribution
        {table | ∃ n, queryOccursAt Value scope bad rule table queryScope query n} ≤
      ∑' tree : {t : ProperTree
          (scopeRelated (observedScope scope queryScope)) none //
          observedTreeValid scope queryScope allowed t},
        tree.1.queryWeight (localMeasure Value distribution queryScope query)
          (allowedDescendantProbability allowed
            (eventProbability Value distribution scope bad)) := by
  let oscope := observedScope scope queryScope
  let obad := observedEvent Value scope bad queryScope query
  have hobad : ∀ label, MeasurableSet (obad label) := by
    intro label
    cases label with
    | none => exact hquery
    | some e => exact hbad e
  calc
    tableMeasure Value distribution
        {table | ∃ n, queryOccursAt Value scope bad rule table queryScope query n} ≤
        tableMeasure Value distribution
          (⋃ tree : {t : ProperTree (scopeRelated oscope) none //
              observedTreeValid scope queryScope allowed t},
            tree.1.passes Value oscope obad) := by
      apply MeasureTheory.measure_mono
      exact queryEverOccurs_subset_iUnion_passes Value scope bad rule queryScope
        query hquery allowed hallowed
    _ ≤ ∑' tree : {t : ProperTree (scopeRelated oscope) none //
          observedTreeValid scope queryScope allowed t},
        tableMeasure Value distribution (tree.1.passes Value oscope obad) :=
      MeasureTheory.measure_iUnion_le _
    _ = ∑' tree : {t : ProperTree (scopeRelated oscope) none //
          observedTreeValid scope queryScope allowed t},
        tree.1.queryWeight (localMeasure Value distribution queryScope query)
          (allowedDescendantProbability allowed
            (eventProbability Value distribution scope bad)) := by
      apply tsum_congr
      intro tree
      rw [tree.1.measure_passes Value distribution oscope obad hobad]
      have hprobability :
          eventProbability Value distribution oscope obad =
            observedProbability (localMeasure Value distribution queryScope query)
              (eventProbability Value distribution scope bad) := by
        funext label
        cases label <;> rfl
      rw [hprobability]
      exact tree.1.weight_observed_eq_queryWeight scope queryScope allowed
        (localMeasure Value distribution queryScope query)
        (eventProbability Value distribution scope bad) tree.2

/-! ## The branching-process estimate for an observed event -/

/-- Odds on allowed bad-event descendants; the observed root has odds zero. -/
noncomputable def allowedOdds (allowed : E → Prop) (x : E → NNReal) :
    Option E → ℝ≥0∞ := by
  classical
  intro label
  exact match label with
    | none => 0
    | some e => if allowed e then (odds x e : ℝ≥0∞) else 0

theorem charge_allowedDescendants (scope : E → Finset I)
    (queryScope : Finset I) (allowed : E → Prop)
    (p : E → ℝ≥0∞) (x : E → NNReal)
    (hcharge : ∀ a, p a * ∏ b : E,
      (if scopeRelated scope a b then 1 + (odds x b : ℝ≥0∞) else 1) ≤
        (odds x a : ℝ≥0∞)) :
    ∀ label : Option E,
      allowedDescendantProbability allowed p label * ∏ child : Option E,
          (if scopeRelated (observedScope scope queryScope) label child
            then 1 + allowedOdds allowed x child else 1) ≤
        allowedOdds allowed x label := by
  classical
  intro label
  cases label with
  | none => simp [allowedDescendantProbability, allowedOdds]
  | some a =>
      by_cases ha : allowed a
      · simp only [allowedDescendantProbability, ha, if_pos, allowedOdds]
        calc
          p a * ∏ child : Option E,
              (if scopeRelated (observedScope scope queryScope) (some a) child
                then 1 + match child with
                  | none => 0
                  | some e => if allowed e then (odds x e : ℝ≥0∞) else 0
                else 1) ≤
              p a * ∏ b : E,
                (if scopeRelated scope a b then 1 + (odds x b : ℝ≥0∞) else 1) := by
            gcongr
            rw [Fintype.prod_option]
            simp only [add_zero, ite_self, one_mul]
            gcongr with b
            have hrel :
                scopeRelated (observedScope scope queryScope) (some a) (some b) ↔
                  scopeRelated scope a b := by
              simp [scopeRelated, observedScope]
            by_cases hro :
                scopeRelated (observedScope scope queryScope) (some a) (some b)
            · have hr := hrel.mp hro
              by_cases hb : allowed b
              · simp [hro, hr, hb]
              · simp [hro, hr, hb]
            · have hr : ¬scopeRelated scope a b := fun h ↦ hro (hrel.mpr h)
              simp [hro, hr]
          _ ≤ (odds x a : ℝ≥0∞) := hcharge a
      · simp [allowedDescendantProbability, allowedOdds, ha]

theorem measure_queryEverOccurs_le_rootProduct
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : ResamplingRule Value scope bad)
    (queryScope : Finset I) (query : Set (LocalAssignment Value queryScope))
    (hquery : MeasurableSet query) (allowed : E → Prop)
    (hallowed : ∀ (assignment : Assignment Value) (e : E),
      ¬queryHolds Value queryScope query assignment →
      rule.choose assignment = some e → allowed e)
    (x : E → NNReal) (hx : ∀ e, x e < 1)
    (hprob : ∀ e, eventProbability Value distribution scope bad e ≤
      (localLemmaBound scope x e : ℝ≥0∞)) :
    tableMeasure Value distribution
        {table | ∃ n, queryOccursAt Value scope bad rule table queryScope query n} ≤
      localMeasure Value distribution queryScope query * ∏ child : Option E,
        (if scopeRelated (observedScope scope queryScope) none child
          then 1 + allowedOdds allowed x child else 1) := by
  let p := eventProbability Value distribution scope bad
  let y := allowedOdds allowed x
  have hbaseCharge : ∀ a, p a * ∏ b : E,
      (if scopeRelated scope a b then 1 + (odds x b : ℝ≥0∞) else 1) ≤
        (odds x a : ℝ≥0∞) :=
    charge_of_localLemmaBound scope p x hx hprob
  have hcharge : ∀ label : Option E,
      allowedDescendantProbability allowed p label * ∏ child : Option E,
          (if scopeRelated (observedScope scope queryScope) label child
            then 1 + y child else 1) ≤ y label :=
    charge_allowedDescendants scope queryScope allowed p x hbaseCharge
  calc
    tableMeasure Value distribution
        {table | ∃ n, queryOccursAt Value scope bad rule table queryScope query n} ≤
        ∑' tree : {t : ProperTree
            (scopeRelated (observedScope scope queryScope)) none //
            observedTreeValid scope queryScope allowed t},
          tree.1.queryWeight (localMeasure Value distribution queryScope query)
            (allowedDescendantProbability allowed p) :=
      measure_queryEverOccurs_le_tsum_queryWeight Value distribution scope bad
        hbad rule queryScope query hquery allowed hallowed
    _ ≤ localMeasure Value distribution queryScope query * ∏ child : Option E,
          (if scopeRelated (observedScope scope queryScope) none child
            then 1 + y child else 1) :=
      ProperTree.tsum_queryWeight_le_of_charge
        (scopeRelated (observedScope scope queryScope))
        (localMeasure Value distribution queryScope query)
        (allowedDescendantProbability allowed p) y hcharge none
        (observedTreeValid scope queryScope allowed)

theorem observedRootProduct_eq (scope : E → Finset I)
    (queryScope : Finset I) (allowed : E → Prop) [DecidablePred allowed]
    (x : E → NNReal) :
    (∏ child : Option E,
        (if scopeRelated (observedScope scope queryScope) none child
          then 1 + allowedOdds allowed x child else 1)) =
      ∏ e : E, if allowed e ∧ ¬Disjoint queryScope (scope e)
        then 1 + (odds x e : ℝ≥0∞) else 1 := by
  classical
  rw [Fintype.prod_option]
  simp only [allowedOdds, add_zero, ite_self, one_mul]
  apply Finset.prod_congr rfl
  intro e _he
  have hrel :
      scopeRelated (observedScope scope queryScope) none (some e) ↔
        ¬Disjoint queryScope (scope e) := by
    simp [scopeRelated, observedScope]
  by_cases hr : scopeRelated (observedScope scope queryScope) none (some e)
  · have hoverlap := hrel.mp hr
    by_cases ha : allowed e
    · simp [hr, hoverlap, ha]
    · simp [hr, hoverlap, ha]
  · have hdisjoint : Disjoint queryScope (scope e) := by
      by_contra hoverlap
      exact hr (hrel.mpr hoverlap)
    simp [hr, hdisjoint]

theorem one_add_odds_eq_inv_one_sub (x : E → NNReal)
    (hx : ∀ e, x e < 1) (e : E) :
    1 + odds x e = (1 - x e)⁻¹ := by
  have hne : 1 - x e ≠ 0 := ne_of_gt (tsub_pos_of_lt (hx e))
  apply mul_left_cancel₀ hne
  rw [one_sub_mul_one_add_odds x hx e, mul_inv_cancel₀ hne]

theorem one_add_coe_odds_eq_coe_inv_one_sub (x : E → NNReal)
    (hx : ∀ e, x e < 1) (e : E) :
    (1 : ℝ≥0∞) + (odds x e : ℝ≥0∞) = ((1 - x e)⁻¹ : NNReal) := by
  rw [← ENNReal.coe_one, ← ENNReal.coe_add,
    one_add_odds_eq_inv_one_sub x hx e]

end ObservedEvent

section HaeuplerSahaSrinivasan

variable {Event : Type} [Fintype Event] [DecidableEq Event]
variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]
variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

theorem haeuplerSahaSrinivasan_rootProduct
    (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (x : BadEventIndex badEvents → NNReal)
    (hx : ∀ A, x A < 1) (B : Event) :
    (∏ child : Option (BadEventIndex badEvents),
        (if scopeRelated
            (observedScope (badEventVariables badEvents variablesOf) (variablesOf B))
            none child
          then 1 + allowedOdds (fun A : BadEventIndex badEvents ↦ A.1 ≠ B) x child
          else 1)) =
      ((∏ C ∈ Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
          badEvents variablesOf B, (1 - x C)⁻¹ : NNReal) : ℝ≥0∞) := by
  classical
  rw [observedRootProduct_eq]
  rw [ENNReal.coe_finsetProd]
  rw [Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro C _hC
  by_cases hneighbor :
      C.1 ≠ B ∧ ¬Disjoint (variablesOf C.1) (variablesOf B)
  · have hneighbor' :
        C.1 ≠ B ∧ ¬Disjoint (variablesOf B) (variablesOf C.1) :=
      ⟨hneighbor.1, fun h ↦ hneighbor.2 h.symm⟩
    simpa [badEventVariables, hneighbor, hneighbor'] using
      one_add_coe_odds_eq_coe_inv_one_sub x hx C
  · have hneighbor' :
        ¬(C.1 ≠ B ∧ ¬Disjoint (variablesOf B) (variablesOf C.1)) := by
      rintro ⟨hne, hoverlap⟩
      exact hneighbor ⟨hne, fun h ↦ hoverlap h.symm⟩
    simp [badEventVariables, hneighbor, hneighbor']

theorem eventOccursInOutput_subset_eventEverOccurs
    (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) :
    eventOccursInOutput Value badEvents variablesOf event selectionRule B ⊆
      eventEverOccurs Value badEvents variablesOf event selectionRule B := by
  intro table houtput
  refine ⟨outputTime Value badEvents variablesOf event selectionRule table, ?_⟩
  simpa [eventOccursAt, eventOccursInOutput, outputAssignment] using houtput

/--
---
conclusion: Lax41.HaeuplerSahaSrinivasanTheorem22.theorem_2_2
---
At the first stage where the observed event is true, adjoin it as a
distinguished root to the execution history.  The resulting proper witness
tree has no further copy of the root and all of its other labels lie in
`Gamma(B)`.  The witness-tree lemma bounds the probability of every such
tree, and the branching-process sum is exactly the local-lemma neighborhood
product.  The output event is a subset of the event that the observation was
true at some stage.
-/
theorem theorem_2_2
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (event_measurable : ∀ A, MeasurableSet (event A))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (x : BadEventIndex badEvents → NNReal)
    (_x_positive : ∀ A, 0 < x A)
    (x_less_than_one : ∀ A, x A < 1)
    (local_lemma_hypothesis : ∀ A,
      eventProbability Value distribution
          (badEventVariables badEvents variablesOf)
          (badEventSet Value badEvents variablesOf event) A ≤
        ((x A * ∏ C ∈
          Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            badEvents variablesOf A.1,
          (1 - x C) : NNReal) : ℝ≥0∞))
    (B : Event) :
    let upperBound :=
      eventProbability Value distribution variablesOf event B *
        ((∏ C ∈ Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
          badEvents variablesOf B, (1 - x C)⁻¹ : NNReal) : ℝ≥0∞)
    probabilityEventEverOccurs Value distribution badEvents variablesOf event
        selectionRule B ≤ upperBound ∧
      probabilityEventInOutput Value distribution badEvents variablesOf event
        selectionRule B ≤ upperBound := by
  classical
  dsimp only
  have hbad : ∀ A : BadEventIndex badEvents,
      MeasurableSet (badEventSet Value badEvents variablesOf event A) := by
    intro A
    exact event_measurable A.1
  have hprob : ∀ A : BadEventIndex badEvents,
      eventProbability Value distribution
          (badEventVariables badEvents variablesOf)
          (badEventSet Value badEvents variablesOf event) A ≤
        (localLemmaBound (badEventVariables badEvents variablesOf) x A : ℝ≥0∞) := by
    intro A
    rw [localLemmaBound_eq_dependencyNeighborhoodProduct
      (badEventVariables badEvents variablesOf) x A]
    have hneighborhood :
        Lax41.MoserTardosDefinitions.dependencyNeighborhood
            (badEventVariables badEvents variablesOf) A =
          Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            badEvents variablesOf A.1 := by
      ext C
      simp [Lax41.MoserTardosDefinitions.dependencyNeighborhood,
      Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood,
        badEventVariables, disjoint_comm]
    rw [hneighborhood]
    exact local_lemma_hypothesis A
  have hallowed : ∀ (assignment : Assignment Value)
      (A : BadEventIndex badEvents),
      ¬queryHolds Value (variablesOf B) (event B) assignment →
      selectionRule.choose assignment = some A → A.1 ≠ B := by
    intro assignment A hquery hchoose hAB
    apply hquery
    subst B
    have htrue := selectionRule.sound hchoose
    simpa [queryHolds, violates, restrictAssignment, badEventVariables,
      badEventSet] using htrue
  have heverRaw := measure_queryEverOccurs_le_rootProduct Value distribution
    (badEventVariables badEvents variablesOf)
    (badEventSet Value badEvents variablesOf event) hbad selectionRule
    (variablesOf B) (event B) (event_measurable B)
    (fun A : BadEventIndex badEvents ↦ A.1 ≠ B) hallowed x x_less_than_one hprob
  have hever :
      probabilityEventEverOccurs Value distribution badEvents variablesOf event
          selectionRule B ≤
        eventProbability Value distribution variablesOf event B *
          ((∏ C ∈ Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            badEvents variablesOf B, (1 - x C)⁻¹ : NNReal) : ℝ≥0∞) := by
    calc
      probabilityEventEverOccurs Value distribution badEvents variablesOf event
          selectionRule B =
          tableMeasure Value distribution
            {table | ∃ n, queryOccursAt Value
              (badEventVariables badEvents variablesOf)
              (badEventSet Value badEvents variablesOf event) selectionRule table
              (variablesOf B) (event B) n} := by
        rfl
      _ ≤ localMeasure Value distribution (variablesOf B) (event B) *
          ∏ child : Option (BadEventIndex badEvents),
            (if scopeRelated
                (observedScope (badEventVariables badEvents variablesOf)
                  (variablesOf B)) none child
              then 1 + allowedOdds
                (fun A : BadEventIndex badEvents ↦ A.1 ≠ B) x child
              else 1) := heverRaw
      _ = eventProbability Value distribution variablesOf event B *
          ((∏ C ∈ Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            badEvents variablesOf B, (1 - x C)⁻¹ : NNReal) : ℝ≥0∞) := by
        rw [haeuplerSahaSrinivasan_rootProduct badEvents variablesOf x x_less_than_one B]
        rfl
  refine ⟨hever, ?_⟩
  calc
    probabilityEventInOutput Value distribution badEvents variablesOf event
        selectionRule B ≤
        probabilityEventEverOccurs Value distribution badEvents variablesOf event
          selectionRule B := by
      exact MeasureTheory.measure_mono
        (eventOccursInOutput_subset_eventEverOccurs Value badEvents variablesOf
          event selectionRule B)
    _ ≤ eventProbability Value distribution variablesOf event B *
          ((∏ C ∈ Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            badEvents variablesOf B, (1 - x C)⁻¹ : NNReal) : ℝ≥0∞) := hever

end HaeuplerSahaSrinivasan

end Lax41Proofs
