import Mathlib
import Lax41.MoserTardos

set_option autoImplicit false

open scoped ENNReal

namespace Lax41Proofs

open Lax41.MoserTardos

variable {E : Type} [Fintype E] [DecidableEq E]

def BTree (E : Type) : Nat → E → Type
  | 0, _ => Fin 0
  | n + 1, _ => (b : E) → Option (BTree E n b)

instance BTree.instFintype : ∀ (n : Nat) (a : E), Fintype (BTree E n a)
  | 0, _ => inferInstanceAs (Fintype (Fin 0))
  | n + 1, _ => by
      letI (b : E) := BTree.instFintype n b
      change Fintype ((b : E) → Option (BTree E n b))
      infer_instance

instance BTree.instDecidableEq : ∀ (n : Nat) (a : E), DecidableEq (BTree E n a)
  | 0, _ => inferInstanceAs (DecidableEq (Fin 0))
  | n + 1, _ => by
      letI (b : E) := BTree.instDecidableEq n b
      change DecidableEq ((b : E) → Option (BTree E n b))
      infer_instance

noncomputable def BTree.weight (r : E → E → Prop) [DecidableRel r]
    (p : E → ℝ≥0∞) :
    {n : Nat} → {a : E} → BTree E n a → ℝ≥0∞
  | 0, _, t => nomatch t
  | _n + 1, a, t =>
      p a * ∏ b, match t b with
        | none => 1
        | some u => if r a b then BTree.weight r p u else 0

theorem BTree.sum_weight_succ (r : E → E → Prop) [DecidableRel r]
    (p : E → ℝ≥0∞) (n : Nat) (a : E) :
    (∑ t : BTree E (n + 1) a, t.weight r p) =
      p a * ∏ b : E, (1 + if r a b then ∑ u : BTree E n b, u.weight r p else 0) := by
  classical
  simp only [BTree.weight, BTree]
  rw [← Finset.mul_sum]
  congr 1
  rw [show (∏ b : E, (1 + if r a b then ∑ u : BTree E n b, u.weight r p else 0)) =
      ∏ b : E, ∑ o : Option (BTree E n b),
        match o with
        | none => 1
        | some u => if r a b then u.weight r p else 0 by
    congr with b
    simp]
  exact (Fintype.prod_sum (fun b (o : Option (BTree E n b)) =>
    match o with
    | none => 1
    | some u => if r a b then u.weight r p else 0)).symm

theorem BTree.sum_weight_le_of_charge (r : E → E → Prop) [DecidableRel r]
    (p y : E → ℝ≥0∞)
    (hcharge : ∀ a, p a * ∏ b : E, (if r a b then 1 + y b else 1) ≤ y a) :
    ∀ (n : Nat) (a : E), ∑ t : BTree E n a, t.weight r p ≤ y a := by
  intro n
  induction n with
  | zero => simp [BTree]
  | succ n ih =>
      intro a
      rw [BTree.sum_weight_succ]
      calc
        p a * ∏ b : E,
            (1 + if r a b then ∑ u : BTree E n b, u.weight r p else 0) ≤
            p a * ∏ b : E, (if r a b then 1 + y b else 1) := by
          gcongr with b
          by_cases hab : r a b
          · simp only [hab, ↓reduceIte]
            simpa [add_comm] using add_le_add_left (ih b) 1
          · simp [hab]
        _ ≤ y a := hcharge a

def pathLabel (root : E) : List E → E
  | [] => root
  | b :: path => pathLabel b path

@[simp]
theorem pathLabel_nil (root : E) : pathLabel root [] = root := rfl

@[simp]
theorem pathLabel_append_singleton (root b : E) (path : List E) :
    pathLabel root (path ++ [b]) = b := by
  induction path generalizing root with
  | nil => rfl
  | cons c path ih => exact ih c

theorem append_singleton_inj {p q : List E} {a b : E} :
    p ++ [a] = q ++ [b] ↔ p = q ∧ a = b := by
  constructor
  · intro h
    have hr := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_singleton] at hr
    injection hr with hab hpq
    exact ⟨List.reverse_injective hpq, hab⟩
  · rintro ⟨rfl, rfl⟩
    rfl

abbrev TimedTree (E : Type) := Finset (Nat × List E)

def TimedTree.candidates (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) : TimedTree E :=
  s.filter fun kp => r (pathLabel root kp.2) e

theorem TimedTree.candidates_subset (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) : s.candidates r root e ⊆ s :=
  Finset.filter_subset _ _

noncomputable def TimedTree.deepest (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (h : (s.candidates r root e).Nonempty) :
    Nat × List E :=
  Classical.choose (Finset.exists_max_image (s.candidates r root e) (List.length ∘ Prod.snd) h)

theorem TimedTree.deepest_mem (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (h : (s.candidates r root e).Nonempty) :
    s.deepest r root e h ∈ s.candidates r root e :=
  (Classical.choose_spec
    (Finset.exists_max_image (s.candidates r root e) (List.length ∘ Prod.snd) h)).1

theorem TimedTree.length_le_deepest (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (h : (s.candidates r root e).Nonempty)
    {kp : Nat × List E} (hkp : kp ∈ s.candidates r root e) :
    kp.2.length ≤ (s.deepest r root e h).2.length :=
  (Classical.choose_spec
    (Finset.exists_max_image (s.candidates r root e) (List.length ∘ Prod.snd) h)).2 kp hkp

noncomputable def TimedTree.insertEarlier (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) : TimedTree E :=
  if h : (s.candidates r root e).Nonempty then
    insert (0, (s.deepest r root e h).2 ++ [e]) s
  else s

def TimedTree.shift (s : TimedTree E) : TimedTree E :=
  s.image fun kp => (kp.1 + 1, kp.2)

noncomputable def buildTimedTree (r : E → E → Prop) [DecidableRel r]
    (root : E) : List E → TimedTree E
  | [] => {(0, [])}
  | e :: history => (buildTimedTree r root history).shift.insertEarlier r root e

def TimedTree.PathsUnique (s : TimedTree E) : Prop :=
  Set.InjOn Prod.snd (↑s : Set (Nat × List E))

def TimedTree.TimesUnique (s : TimedTree E) : Prop :=
  Set.InjOn Prod.fst (↑s : Set (Nat × List E))

def TimedTree.Chronological (r : E → E → Prop) (root : E)
    (s : TimedTree E) : Prop :=
  ∀ ⦃kp lq : Nat × List E⦄, kp ∈ s → lq ∈ s → kp.1 < lq.1 →
    r (pathLabel root kp.2) (pathLabel root lq.2) → lq.2.length < kp.2.length

def TimedTree.Represents (root : E) (history : List E) (s : TimedTree E) : Prop :=
  ∀ ⦃kp : Nat × List E⦄, kp ∈ s →
    history[kp.1]? = some (pathLabel root kp.2) ∨
      (kp.1 = history.length ∧ kp.2 = [])

def TimedTree.Closed (r : E → E → Prop) (root : E)
    (history : List E) (s : TimedTree E) : Prop :=
  ∀ ⦃lq : Nat × List E⦄, lq ∈ s → ∀ ⦃k : Nat⦄ ⦃e : E⦄,
    history[k]? = some e → k < lq.1 →
      r e (pathLabel root lq.2) → ∃ p, (k, p) ∈ s

def TimedTree.PrefixClosed (s : TimedTree E) : Prop :=
  ∀ ⦃kp : Nat × List E⦄, kp ∈ s → ∀ ⦃q : List E⦄ ⦃e : E⦄,
    kp.2 = q ++ [e] → ∃ k, (k, q) ∈ s

def TimedTree.EdgeValid (r : E → E → Prop) (root : E)
    (s : TimedTree E) : Prop :=
  ∀ ⦃kp : Nat × List E⦄, kp ∈ s → ∀ ⦃q : List E⦄ ⦃e : E⦄,
    kp.2 = q ++ [e] → r (pathLabel root q) e

def TimedTree.DepthBound (history : List E) (s : TimedTree E) : Prop :=
  ∀ ⦃kp : Nat × List E⦄, kp ∈ s → kp.2.length ≤ history.length

@[simp]
theorem TimedTree.mem_shift {s : TimedTree E} {kp : Nat × List E} :
    kp ∈ s.shift ↔ ∃ old ∈ s, (old.1 + 1, old.2) = kp := by
  simp [TimedTree.shift]

theorem TimedTree.shift_pathsUnique {s : TimedTree E} (h : s.PathsUnique) :
    s.shift.PathsUnique := by
  rw [TimedTree.PathsUnique] at h ⊢
  intro kp hkp lq hlq heq
  change kp ∈ s.shift at hkp
  change lq ∈ s.shift at hlq
  rw [TimedTree.mem_shift] at hkp hlq
  obtain ⟨kp', hkp', hkp_eq⟩ := hkp
  obtain ⟨lq', hlq', hlq_eq⟩ := hlq
  subst kp
  subst lq
  have hsnd : kp'.2 = lq'.2 := by simpa using heq
  have hpairs : kp' = lq' := h hkp' hlq' hsnd
  subst lq'
  rfl

theorem TimedTree.shift_timesUnique {s : TimedTree E} (h : s.TimesUnique) :
    s.shift.TimesUnique := by
  rw [TimedTree.TimesUnique] at h ⊢
  intro kp hkp lq hlq heq
  change kp ∈ s.shift at hkp
  change lq ∈ s.shift at hlq
  rw [TimedTree.mem_shift] at hkp hlq
  obtain ⟨kp', hkp', hkp_eq⟩ := hkp
  obtain ⟨lq', hlq', hlq_eq⟩ := hlq
  subst kp
  subst lq
  have hfst : kp'.1 = lq'.1 := by omega
  have hpairs : kp' = lq' := h hkp' hlq' hfst
  subst lq'
  rfl

theorem TimedTree.deepest_in_tree (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (h : (s.candidates r root e).Nonempty) :
    s.deepest r root e h ∈ s :=
  s.candidates_subset r root e (s.deepest_mem r root e h)

theorem TimedTree.deepest_related (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (h : (s.candidates r root e).Nonempty) :
    r (pathLabel root (s.deepest r root e h).2) e := by
  have hm := s.deepest_mem r root e h
  simpa [TimedTree.candidates] using (Finset.mem_filter.mp hm).2

theorem TimedTree.newPath_fresh (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (root e : E) (s : TimedTree E)
    (h : (s.candidates r root e).Nonempty) :
    ∀ kp ∈ s, kp.2 ≠ (s.deepest r root e h).2 ++ [e] := by
  intro kp hkp heq
  have hrel : r (pathLabel root kp.2) e := by
    rw [heq, pathLabel_append_singleton]
    exact hrefl e
  have hcand : kp ∈ s.candidates r root e := by
    simp [TimedTree.candidates, hkp, hrel]
  have hle := s.length_le_deepest r root e h hcand
  rw [heq, List.length_append] at hle
  simp at hle

theorem TimedTree.insertEarlier_pathsUnique (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (root e : E) (s : TimedTree E) (hs : s.PathsUnique) :
    (s.insertEarlier r root e).PathsUnique := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs with h
  swap
  · exact hs
  rw [TimedTree.PathsUnique] at hs ⊢
  intro kp hkp lq hlq heq
  change kp ∈ insert (0, (s.deepest r root e h).2 ++ [e]) s at hkp
  change lq ∈ insert (0, (s.deepest r root e h).2 ++ [e]) s at hlq
  simp only [Finset.mem_insert] at hkp hlq
  rcases hkp with rfl | hkp <;> rcases hlq with rfl | hlq
  · rfl
  · exact False.elim (s.newPath_fresh r hrefl root e h _ hlq heq.symm)
  · exact False.elim (s.newPath_fresh r hrefl root e h _ hkp heq)
  · exact hs hkp hlq heq

theorem TimedTree.insertEarlier_timesUnique (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (hs : s.TimesUnique)
    (hpositive : ∀ kp ∈ s, 0 < kp.1) :
    (s.insertEarlier r root e).TimesUnique := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs
  swap
  · exact hs
  rw [TimedTree.TimesUnique] at hs ⊢
  intro kp hkp lq hlq heq
  change kp ∈ insert (0, (s.deepest r root e ‹_›).2 ++ [e]) s at hkp
  change lq ∈ insert (0, (s.deepest r root e ‹_›).2 ++ [e]) s at hlq
  simp only [Finset.mem_insert] at hkp hlq
  rcases hkp with rfl | hkp <;> rcases hlq with rfl | hlq
  · rfl
  · simp only [Prod.fst] at heq
    exact False.elim (Nat.ne_of_gt (hpositive _ hlq) heq.symm)
  · simp only [Prod.fst] at heq
    exact False.elim (Nat.ne_of_gt (hpositive _ hkp) heq)
  · exact hs hkp hlq heq

theorem TimedTree.insertEarlier_chronological (r : E → E → Prop) [DecidableRel r]
    (hsymm : Symmetric r) (root e : E) (s : TimedTree E)
    (hchron : s.Chronological r root) (hpositive : ∀ kp ∈ s, 0 < kp.1) :
    (s.insertEarlier r root e).Chronological r root := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs with h
  swap
  · exact hchron
  intro kp lq hkp hlq htime hrel
  simp only [Finset.mem_insert] at hkp hlq
  rcases hkp with rfl | hkp
  · rcases hlq with rfl | hlq
    · simp at htime
    · have hlq_cand : lq ∈ s.candidates r root e := by
        apply Finset.mem_filter.mpr
        refine ⟨hlq, ?_⟩
        simpa [pathLabel_append_singleton] using
          hsymm (by simpa [pathLabel_append_singleton] using hrel)
      have hle := s.length_le_deepest r root e h hlq_cand
      simpa using Nat.lt_succ_of_le hle
  · rcases hlq with rfl | hlq
    · exact False.elim (Nat.not_lt_zero _ htime)
    · exact hchron hkp hlq htime hrel

theorem TimedTree.shift_chronological (r : E → E → Prop) (root : E)
    {s : TimedTree E} (h : s.Chronological r root) :
    s.shift.Chronological r root := by
  intro kp lq hkp hlq htime hrel
  rw [TimedTree.mem_shift] at hkp hlq
  obtain ⟨kp', hkp', hkp_eq⟩ := hkp
  obtain ⟨lq', hlq', hlq_eq⟩ := hlq
  subst kp
  subst lq
  apply h hkp' hlq'
  · omega
  · exact hrel

theorem TimedTree.shift_represents (root e : E) (history : List E)
    {s : TimedTree E} (h : s.Represents root history) :
    s.shift.Represents root (e :: history) := by
  intro kp hkp
  rw [TimedTree.mem_shift] at hkp
  obtain ⟨old, hold, rfl⟩ := hkp
  rcases h hold with hlabel | ⟨htime, hpath⟩
  · left
    simpa using hlabel
  · right
    simp only [List.length_cons]
    exact ⟨by omega, hpath⟩

theorem TimedTree.shift_prefixClosed {s : TimedTree E} (h : s.PrefixClosed) :
    s.shift.PrefixClosed := by
  intro kp hkp q e hpath
  rw [TimedTree.mem_shift] at hkp
  obtain ⟨old, hold, hEq⟩ := hkp
  subst kp
  obtain ⟨k, hk⟩ := h hold hpath
  exact ⟨k + 1, by
    rw [TimedTree.mem_shift]
    exact ⟨(k, q), hk, rfl⟩⟩

theorem TimedTree.shift_edgeValid (r : E → E → Prop) (root : E)
    {s : TimedTree E} (h : s.EdgeValid r root) : s.shift.EdgeValid r root := by
  intro kp hkp q e hpath
  rw [TimedTree.mem_shift] at hkp
  obtain ⟨old, hold, hEq⟩ := hkp
  subst kp
  exact h hold hpath

theorem TimedTree.shift_depthBound (e : E) (history : List E)
    {s : TimedTree E} (h : s.DepthBound history) :
    s.shift.DepthBound (e :: history) := by
  intro kp hkp
  rw [TimedTree.mem_shift] at hkp
  obtain ⟨old, hold, rfl⟩ := hkp
  exact (h hold).trans (by simp)

theorem TimedTree.shift_positive {s : TimedTree E} :
    ∀ kp ∈ s.shift, 0 < kp.1 := by
  intro kp hkp
  rw [TimedTree.mem_shift] at hkp
  obtain ⟨old, _hold, rfl⟩ := hkp
  omega

theorem TimedTree.insertEarlier_represents (r : E → E → Prop) [DecidableRel r]
    (root e : E) (history : List E) (s : TimedTree E)
    (hrep : s.Represents root (e :: history)) :
    (s.insertEarlier r root e).Represents root (e :: history) := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs with h
  swap
  · exact hrep
  intro kp hkp
  simp only [Finset.mem_insert] at hkp
  rcases hkp with rfl | hkp
  · left
    simp [pathLabel_append_singleton]
  · exact hrep hkp

theorem TimedTree.insertEarlier_prefixClosed (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (hpref : s.PrefixClosed) :
    (s.insertEarlier r root e).PrefixClosed := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs with h
  swap
  · exact hpref
  intro kp hkp q f hpath
  simp only [Finset.mem_insert] at hkp
  rcases hkp with rfl | hkp
  · obtain ⟨hq, _⟩ := append_singleton_inj.mp hpath
    subst q
    exact ⟨(s.deepest r root e h).1, by
      exact Finset.mem_insert_of_mem (s.deepest_in_tree r root e h)⟩
  · obtain ⟨k, hk⟩ := hpref hkp hpath
    exact ⟨k, Finset.mem_insert_of_mem hk⟩

theorem TimedTree.insertEarlier_edgeValid (r : E → E → Prop) [DecidableRel r]
    (root e : E) (s : TimedTree E) (hedge : s.EdgeValid r root) :
    (s.insertEarlier r root e).EdgeValid r root := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs with h
  swap
  · exact hedge
  intro kp hkp q f hpath
  simp only [Finset.mem_insert] at hkp
  rcases hkp with rfl | hkp
  · obtain ⟨hq, hf⟩ := append_singleton_inj.mp hpath
    subst q
    subst f
    exact s.deepest_related r root e h
  · exact hedge hkp hpath

theorem TimedTree.insertEarlier_depthBound (r : E → E → Prop) [DecidableRel r]
    (root e : E) (history : List E) (s : TimedTree E)
    (hdepth : ∀ kp ∈ s, kp.2.length ≤ history.length) :
    (s.insertEarlier r root e).DepthBound (e :: history) := by
  classical
  unfold TimedTree.insertEarlier
  split_ifs with h
  · intro kp hkp
    simp only [Finset.mem_insert] at hkp
    rcases hkp with rfl | hkp
    · simp only [Prod.snd, List.length_append, List.length_singleton, List.length_cons]
      exact Nat.add_le_add_right (hdepth _ (s.deepest_in_tree r root e h)) 1
    · exact (hdepth _ hkp).trans (by simp)
  · intro kp hkp
    exact (hdepth _ hkp).trans (by simp)

structure TimedTree.Good (r : E → E → Prop) (root : E) (history : List E)
    (s : TimedTree E) : Prop where
  pathsUnique : s.PathsUnique
  timesUnique : s.TimesUnique
  chronological : s.Chronological r root
  represents : s.Represents root history
  closed : s.Closed r root history
  prefixClosed : s.PrefixClosed
  edgeValid : s.EdgeValid r root
  depthBound : s.DepthBound history
  root_mem : (history.length, []) ∈ s

theorem buildTimedTree_good (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    (buildTimedTree r root history).Good r root history := by
  induction history with
  | nil =>
      constructor <;> simp [buildTimedTree, TimedTree.PathsUnique,
        TimedTree.TimesUnique, TimedTree.Chronological, TimedTree.Represents,
        TimedTree.Closed, TimedTree.PrefixClosed, TimedTree.EdgeValid,
        TimedTree.DepthBound]
  | cons e history ih =>
      let old := buildTimedTree r root history
      let shifted := old.shift
      have hold_paths : old.PathsUnique := by simpa [old] using ih.pathsUnique
      have hold_times : old.TimesUnique := by simpa [old] using ih.timesUnique
      have hold_chron : old.Chronological r root := by simpa [old] using ih.chronological
      have hold_rep : old.Represents root history := by simpa [old] using ih.represents
      have hold_closed : old.Closed r root history := by simpa [old] using ih.closed
      have hold_pref : old.PrefixClosed := by simpa [old] using ih.prefixClosed
      have hold_edge : old.EdgeValid r root := by simpa [old] using ih.edgeValid
      have hold_depth : old.DepthBound history := by simpa [old] using ih.depthBound
      have hold_root : (history.length, []) ∈ old := by simpa [old] using ih.root_mem
      have hshift_paths : shifted.PathsUnique :=
        TimedTree.shift_pathsUnique (s := old) hold_paths
      have hshift_times : shifted.TimesUnique :=
        TimedTree.shift_timesUnique (s := old) hold_times
      have hshift_chron : shifted.Chronological r root :=
        TimedTree.shift_chronological r root hold_chron
      have hshift_rep : shifted.Represents root (e :: history) :=
        TimedTree.shift_represents root e history hold_rep
      have hshift_pref : shifted.PrefixClosed :=
        TimedTree.shift_prefixClosed hold_pref
      have hshift_edge : shifted.EdgeValid r root :=
        TimedTree.shift_edgeValid r root hold_edge
      have hshift_positive : ∀ kp ∈ shifted, 0 < kp.1 := TimedTree.shift_positive
      have hshift_depth_old : ∀ kp ∈ shifted, kp.2.length ≤ history.length := by
        intro kp hkp
        change kp ∈ old.shift at hkp
        rw [TimedTree.mem_shift] at hkp
        obtain ⟨source, hsource, hsource_eq⟩ := hkp
        have hs := hold_depth hsource
        simpa [← hsource_eq] using hs
      have hclosed : (shifted.insertEarlier r root e).Closed r root (e :: history) := by
        classical
        unfold TimedTree.insertEarlier
        split_ifs with hcand
        · intro lq hlq k f hk hkl hrel
          simp only [Finset.mem_insert] at hlq
          rcases hlq with rfl | hlq
          · simp at hkl
          · rw [TimedTree.mem_shift] at hlq
            obtain ⟨source, hsource, hsource_eq⟩ := hlq
            subst lq
            cases k with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
                subst f
                exact ⟨(shifted.deepest r root e hcand).2 ++ [e], by simp⟩
            | succ k =>
                simp only [List.getElem?_cons_succ] at hk
                obtain ⟨p, hp⟩ := hold_closed hsource hk (by omega) hrel
                exact ⟨p, Finset.mem_insert_of_mem (by
                  rw [TimedTree.mem_shift]
                  exact ⟨(k, p), hp, rfl⟩)⟩
        · intro lq hlq k f hk hkl hrel
          rw [TimedTree.mem_shift] at hlq
          obtain ⟨source, hsource, hsource_eq⟩ := hlq
          subst lq
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
              subst f
              exfalso
              apply hcand
              refine ⟨(source.1 + 1, source.2), ?_⟩
              apply Finset.mem_filter.mpr
              refine ⟨?_, hsymm hrel⟩
              rw [TimedTree.mem_shift]
              exact ⟨source, hsource, rfl⟩
          | succ k =>
              simp only [List.getElem?_cons_succ] at hk
              obtain ⟨p, hp⟩ := hold_closed hsource hk (by omega) hrel
              exact ⟨p, by
                rw [TimedTree.mem_shift]
                exact ⟨(k, p), hp, rfl⟩⟩
      refine {
        pathsUnique := TimedTree.insertEarlier_pathsUnique r hrefl root e shifted hshift_paths
        timesUnique := TimedTree.insertEarlier_timesUnique r root e shifted hshift_times
          hshift_positive
        chronological := TimedTree.insertEarlier_chronological r hsymm root e shifted
          hshift_chron hshift_positive
        represents := TimedTree.insertEarlier_represents r root e history shifted hshift_rep
        closed := hclosed
        prefixClosed := TimedTree.insertEarlier_prefixClosed r root e shifted hshift_pref
        edgeValid := TimedTree.insertEarlier_edgeValid r root e shifted hshift_edge
        depthBound := TimedTree.insertEarlier_depthBound r root e history shifted hshift_depth_old
        root_mem := ?_ }
      change ((e :: history).length, []) ∈ shifted.insertEarlier r root e
      unfold TimedTree.insertEarlier
      split_ifs
      · exact Finset.mem_insert_of_mem (by
          rw [TimedTree.mem_shift]
          exact ⟨(history.length, []), hold_root, by simp⟩)
      · rw [TimedTree.mem_shift]
        exact ⟨(history.length, []), hold_root, by simp⟩

def TimedTree.paths (s : TimedTree E) : Finset (List E) := s.image Prod.snd

@[simp]
theorem TimedTree.mem_paths {s : TimedTree E} {p : List E} :
    p ∈ s.paths ↔ ∃ k, (k, p) ∈ s := by
  simp [TimedTree.paths]

def BTree.paths : {n : Nat} → {a : E} → BTree E n a → Finset (List E)
  | 0, _, t => nomatch t
  | _n + 1, _a, t =>
      insert [] <| Finset.univ.biUnion fun b =>
        match t b with
        | none => ∅
        | some u => u.paths.image (b :: ·)

@[simp]
theorem BTree.nil_mem_paths {n : Nat} {a : E} (t : BTree E (n + 1) a) :
    [] ∈ t.paths := by
  simp [BTree.paths]

@[simp]
theorem BTree.cons_mem_paths {n : Nat} {a b : E} (q : List E)
    (t : BTree E (n + 1) a) :
    b :: q ∈ t.paths ↔ ∃ u, t b = some u ∧ q ∈ u.paths := by
  classical
  simp only [BTree.paths, Finset.mem_insert, List.cons_ne_nil, false_or,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc⟩
    cases htc : t c with
    | none => simp [htc] at hc
    | some u =>
        rw [htc] at hc
        obtain ⟨q', hq', heq⟩ := Finset.mem_image.mp hc
        injection heq with hcb hqq
        subst c
        subst q'
        exact ⟨u, htc, hq'⟩
  · rintro ⟨u, htu, hq⟩
    refine ⟨b, ?_⟩
    simp [htu, hq]

def ChildPaths (b : E) (S : Finset (List E)) : Finset (List E) :=
  (S.filter fun p => p.head? = some b).image List.tail

@[simp]
theorem mem_childPaths {b : E} {S : Finset (List E)} {q : List E} :
    q ∈ ChildPaths b S ↔ b :: q ∈ S := by
  classical
  constructor
  · intro hq
    obtain ⟨p, hp, htail⟩ := Finset.mem_image.mp hq
    have hhead : p.head? = some b := (Finset.mem_filter.mp hp).2
    have hpcons : p = b :: q := by
      cases p with
      | nil => simp at hhead
      | cons c p =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst c
          simpa using htail
    simpa [hpcons] using (Finset.mem_filter.mp hp).1
  · intro hq
    apply Finset.mem_image.mpr
    exact ⟨b :: q, by simp [ChildPaths, hq], rfl⟩

def PathsPrefixClosed (S : Finset (List E)) : Prop :=
  ∀ ⦃q : List E⦄ ⦃b : E⦄, q ++ [b] ∈ S → q ∈ S

theorem first_mem_of_cons_mem {b : E} {q : List E} {S : Finset (List E)}
    (hprefix : PathsPrefixClosed S) (hmem : b :: q ∈ S) : [b] ∈ S := by
  induction q using List.reverseRecOn with
  | nil => simpa using hmem
  | append_singleton q c ih =>
      apply ih
      apply hprefix
      simpa [List.cons_append] using hmem

theorem childPaths_nil_mem {b : E} {S : Finset (List E)}
    (hprefix : PathsPrefixClosed S) (hb : [b] ∈ S) : [] ∈ ChildPaths b S := by
  simpa using hb

theorem childPaths_prefixClosed {b : E} {S : Finset (List E)}
    (hprefix : PathsPrefixClosed S) : PathsPrefixClosed (ChildPaths b S) := by
  intro q c hqc
  rw [mem_childPaths] at hqc ⊢
  have heq : b :: (q ++ [c]) = (b :: q) ++ [c] := by simp
  rw [heq] at hqc
  exact hprefix hqc

theorem BTree.exists_paths_eq (n : Nat) (a : E) (S : Finset (List E))
    (hroot : [] ∈ S) (hdepth : ∀ p ∈ S, p.length < n + 1)
    (hprefix : PathsPrefixClosed S) :
    ∃ t : BTree E (n + 1) a, t.paths = S := by
  induction n generalizing a S with
  | zero =>
      let t : BTree E 1 a := fun _ => none
      refine ⟨t, ?_⟩
      ext p
      cases p with
      | nil => simpa [t] using hroot
      | cons b q =>
          have hnot : b :: q ∉ S := by
            intro hmem
            have := hdepth _ hmem
            simp at this
          simp [t, hnot]
  | succ n ih =>
      have hchild (b : E) (hb : [b] ∈ S) :
          ∃ u : BTree E (n + 1) b, u.paths = ChildPaths b S := by
        apply ih
        · exact childPaths_nil_mem hprefix hb
        · intro q hq
          rw [mem_childPaths] at hq
          have hd := hdepth _ hq
          simpa using hd
        · exact childPaths_prefixClosed hprefix
      let child (b : E) : Option (BTree E (n + 1) b) :=
        if hb : [b] ∈ S then some (Classical.choose (hchild b hb)) else none
      let t : BTree E (n + 2) a := child
      refine ⟨t, ?_⟩
      ext p
      cases p with
      | nil => simpa [t] using hroot
      | cons b q =>
          by_cases hb : [b] ∈ S
          · have hchosen := Classical.choose_spec (hchild b hb)
            simp [t, child, hb, hchosen]
          · have hnot : b :: q ∉ S := by
              intro hmem
              exact hb (first_mem_of_cons_mem hprefix hmem)
            simp [t, child, hb, hnot]

theorem TimedTree.Good.paths_root_mem {r : E → E → Prop} {root : E}
    {history : List E} {s : TimedTree E} (h : s.Good r root history) :
    [] ∈ s.paths := by
  rw [TimedTree.mem_paths]
  exact ⟨history.length, h.root_mem⟩

theorem TimedTree.Good.paths_depth {r : E → E → Prop} {root : E}
    {history : List E} {s : TimedTree E} (h : s.Good r root history) :
    ∀ p ∈ s.paths, p.length < history.length + 1 := by
  intro p hp
  rw [TimedTree.mem_paths] at hp
  obtain ⟨k, hk⟩ := hp
  exact Nat.lt_succ_of_le (h.depthBound hk)

theorem TimedTree.Good.paths_prefixClosed {r : E → E → Prop} {root : E}
    {history : List E} {s : TimedTree E} (h : s.Good r root history) :
    PathsPrefixClosed s.paths := by
  intro q b hqb
  rw [TimedTree.mem_paths] at hqb ⊢
  obtain ⟨k, hk⟩ := hqb
  obtain ⟨l, hl⟩ := h.prefixClosed hk rfl
  exact ⟨l, hl⟩

theorem TimedTree.Good.paths_edgeValid {r : E → E → Prop} {root : E}
    {history : List E} {s : TimedTree E} (h : s.Good r root history) :
    ∀ ⦃q : List E⦄ ⦃b : E⦄, q ++ [b] ∈ s.paths → r (pathLabel root q) b := by
  intro q b hqb
  rw [TimedTree.mem_paths] at hqb
  obtain ⟨k, hk⟩ := hqb
  exact h.edgeValid hk rfl

noncomputable def witnessTree (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    BTree E (history.length + 1) root :=
  Classical.choose <| BTree.exists_paths_eq history.length root
    (buildTimedTree r root history).paths
    (buildTimedTree_good r hrefl hsymm root history).paths_root_mem
    (buildTimedTree_good r hrefl hsymm root history).paths_depth
    (buildTimedTree_good r hrefl hsymm root history).paths_prefixClosed

theorem witnessTree_paths (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    (witnessTree r hrefl hsymm root history).paths =
      (buildTimedTree r root history).paths :=
  Classical.choose_spec <| BTree.exists_paths_eq history.length root
    (buildTimedTree r root history).paths
    (buildTimedTree_good r hrefl hsymm root history).paths_root_mem
    (buildTimedTree_good r hrefl hsymm root history).paths_depth
    (buildTimedTree_good r hrefl hsymm root history).paths_prefixClosed

def TimedTree.labelCount (root label : E) (s : TimedTree E) : Nat :=
  (s.paths.filter fun p => pathLabel root p = label).card

theorem TimedTree.shift_paths (s : TimedTree E) : s.shift.paths = s.paths := by
  classical
  ext p
  simp only [TimedTree.mem_paths, TimedTree.mem_shift]
  constructor
  · rintro ⟨k, old, hold, heq⟩
    have hp : old.2 = p := congrArg Prod.snd heq
    subst p
    exact ⟨old.1, hold⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, (k, p), hk, rfl⟩

theorem TimedTree.shift_labelCount (root label : E) (s : TimedTree E) :
    s.shift.labelCount root label = s.labelCount root label := by
  simp [TimedTree.labelCount, TimedTree.shift_paths]

theorem TimedTree.insertEarlier_labelCount (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (root e label : E) (s : TimedTree E) :
    (s.insertEarlier r root e).labelCount root label =
      if (s.candidates r root e).Nonempty ∧ e = label then
        s.labelCount root label + 1
      else s.labelCount root label := by
  classical
  by_cases hcand : (s.candidates r root e).Nonempty
  · rw [TimedTree.insertEarlier, dif_pos hcand]
    have hfresh := s.newPath_fresh r hrefl root e hcand
    have hpath_not : (s.deepest r root e hcand).2 ++ [e] ∉ s.paths := by
      rw [TimedTree.mem_paths]
      rintro ⟨k, hk⟩
      exact hfresh (k, (s.deepest r root e hcand).2 ++ [e]) hk rfl
    by_cases he : e = label
    · rw [if_pos ⟨hcand, he⟩]
      subst e
      rw [TimedTree.labelCount, TimedTree.paths, Finset.image_insert,
        Finset.filter_insert, if_pos (by simp)]
      have hfilter_not : (s.deepest r root label hcand).2 ++ [label] ∉
          (s.paths.filter fun p => pathLabel root p = label) := by
        intro hmem
        exact hpath_not (Finset.mem_filter.mp hmem).1
      change (insert ((s.deepest r root label hcand).2 ++ [label])
          (s.paths.filter fun p => pathLabel root p = label)).card =
        s.labelCount root label + 1
      rw [Finset.card_insert_of_notMem hfilter_not]
      rfl
    · rw [if_neg (by simp [he])]
      rw [TimedTree.labelCount, TimedTree.paths, Finset.image_insert,
        Finset.filter_insert, if_neg (by simpa using he)]
      rfl
  · rw [TimedTree.insertEarlier, dif_neg hcand, if_neg (by simp [hcand])]

theorem buildTimedTree_root_labelCount (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    (buildTimedTree r root history).labelCount root root = history.count root + 1 := by
  classical
  induction history with
  | nil =>
      rw [buildTimedTree, TimedTree.labelCount, TimedTree.paths,
        Finset.image_singleton]
      rw [Finset.filter_eq_self.mpr]
      · simp
      · intro p hp
        simp only [Finset.mem_singleton] at hp
        subst p
        rfl
  | cons e history ih =>
      rw [buildTimedTree]
      let s := (buildTimedTree r root history).shift
      have hsroot : ∃ k, (k, []) ∈ s := by
        exact ⟨history.length + 1, by
          rw [TimedTree.mem_shift]
          exact ⟨(history.length, []),
            (buildTimedTree_good r hrefl hsymm root history).root_mem, by simp⟩⟩
      rw [TimedTree.insertEarlier_labelCount r hrefl root e root s,
        TimedTree.shift_labelCount, ih]
      by_cases he : e = root
      · subst e
        have hcand : (s.candidates r root root).Nonempty := by
          obtain ⟨k, hk⟩ := hsroot
          exact ⟨(k, []), Finset.mem_filter.mpr ⟨hk, hrefl root⟩⟩
        simp [hcand, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [he]

def BTree.labelCount {n : Nat} {a : E} (root label : E) (t : BTree E n a) : Nat :=
  (t.paths.filter fun p => pathLabel root p = label).card

theorem witnessTree_root_labelCount (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    (witnessTree r hrefl hsymm root history).labelCount root root =
      history.count root + 1 := by
  rw [BTree.labelCount, witnessTree_paths]
  exact buildTimedTree_root_labelCount r hrefl hsymm root history

def BTree.StronglyProper (r : E → E → Prop) (root : E)
    {n : Nat} {a : E} (t : BTree E n a) : Prop :=
  ∀ ⦃p q : List E⦄, p ∈ t.paths → q ∈ t.paths → p.length = q.length →
    r (pathLabel root p) (pathLabel root q) → p = q

theorem TimedTree.Good.paths_stronglyProper {r : E → E → Prop} {root : E}
    {history : List E} {s : TimedTree E} (h : s.Good r root history)
    (hsymm : Symmetric r) :
    ∀ ⦃p q : List E⦄, p ∈ s.paths → q ∈ s.paths → p.length = q.length →
      r (pathLabel root p) (pathLabel root q) → p = q := by
  intro p q hp hq hlength hrelated
  rw [TimedTree.mem_paths] at hp hq
  obtain ⟨k, hk⟩ := hp
  obtain ⟨l, hl⟩ := hq
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hlt := h.chronological hk hl hkl hrelated
    change q.length < p.length at hlt
    omega
  · have hpairs : (k, p) = (l, q) := h.timesUnique hk hl hkl
    exact congrArg Prod.snd hpairs
  · have hlt := h.chronological hl hk hkl (hsymm hrelated)
    change p.length < q.length at hlt
    omega

theorem witnessTree_stronglyProper (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    (witnessTree r hrefl hsymm root history).StronglyProper r root := by
  intro p q hp hq hlength hrelated
  rw [witnessTree_paths] at hp hq
  exact (buildTimedTree_good r hrefl hsymm root history).paths_stronglyProper hsymm
    hp hq hlength hrelated

def BTree.childBlock {n : Nat} {a : E} (t : BTree E (n + 1) a) (b : E) :
    Finset (List E) :=
  match t b with
  | none => ∅
  | some u => u.paths.image (b :: ·)

theorem BTree.paths_eq_insert_biUnion {n : Nat} {a : E} (t : BTree E (n + 1) a) :
    t.paths = insert [] (Finset.univ.biUnion t.childBlock) := by
  rfl

theorem BTree.nil_not_mem_childBlock {n : Nat} {a b : E} (t : BTree E (n + 1) a) :
    [] ∉ t.childBlock b := by
  cases htb : t b with
  | none => simp [BTree.childBlock, htb]
  | some u => simp [BTree.childBlock, htb]

theorem BTree.head?_eq_of_mem_childBlock {n : Nat} {a b : E}
    {t : BTree E (n + 1) a} {p : List E} (hp : p ∈ t.childBlock b) :
    p.head? = some b := by
  cases htb : t b with
  | none => simp [BTree.childBlock, htb] at hp
  | some u =>
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp (by simpa [BTree.childBlock, htb] using hp)
      simp

theorem BTree.childBlock_pairwiseDisjoint {n : Nat} {a : E}
    (t : BTree E (n + 1) a) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset E)) t.childBlock := by
  intro b _hb c _hc hbc
  change Disjoint (t.childBlock b) (t.childBlock c)
  rw [Finset.disjoint_left]
  intro p hpb hpc
  have hb := t.head?_eq_of_mem_childBlock hpb
  have hc := t.head?_eq_of_mem_childBlock hpc
  rw [hb] at hc
  exact hbc (Option.some.inj hc)

noncomputable def BTree.pathWeight (p : E → ℝ≥0∞) (root : E) {n : Nat} {a : E}
    (t : BTree E n a) : ℝ≥0∞ :=
  ∏ q ∈ t.paths, p (pathLabel root q)

theorem BTree.pathWeight_succ (p : E → ℝ≥0∞) (n : Nat) (a : E)
    (t : BTree E (n + 1) a) :
    t.pathWeight p a = p a * ∏ b : E, match t b with
      | none => 1
      | some u => u.pathWeight p b := by
  classical
  rw [BTree.pathWeight, BTree.paths_eq_insert_biUnion,
    Finset.prod_insert (by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      push_neg
      exact fun b ↦ t.nil_not_mem_childBlock)]
  change p a * ∏ x ∈ Finset.univ.biUnion t.childBlock, p (pathLabel a x) = _
  congr 1
  rw [Finset.prod_biUnion t.childBlock_pairwiseDisjoint]
  apply Finset.prod_congr rfl
  intro b _hb
  cases htb : t b with
  | none => simp [BTree.childBlock, htb]
  | some u =>
      rw [show t.childBlock b = u.paths.image (b :: ·) by simp [BTree.childBlock, htb],
        Finset.prod_image]
      · rfl
      · intro q _hq q' _hq' heq
        exact List.cons.inj heq |>.2

def BTree.EdgeValid (r : E → E → Prop) (root : E) {n : Nat} {a : E}
    (t : BTree E n a) : Prop :=
  ∀ ⦃q : List E⦄ ⦃b : E⦄, q ++ [b] ∈ t.paths → r (pathLabel root q) b

theorem BTree.child_edgeValid {r : E → E → Prop} {root : E} {n : Nat} {a b : E}
    {t : BTree E (n + 1) a} {u : BTree E n b} (htb : t b = some u)
    (hvalid : t.EdgeValid r root) : u.EdgeValid r b := by
  intro q c hqc
  apply hvalid (q := b :: q) (b := c)
  rw [List.cons_append]
  exact BTree.cons_mem_paths (q ++ [c]) t |>.2 ⟨u, htb, hqc⟩

theorem BTree.root_related_of_child {r : E → E → Prop} {root : E}
    {n : Nat} {a b : E} {t : BTree E (n + 1) a} {u : BTree E n b}
    (htb : t b = some u) (hvalid : t.EdgeValid r root) : r root b := by
  cases n with
  | zero => exact Fin.elim0 u
  | succ n =>
      apply hvalid (q := []) (b := b)
      simpa using BTree.cons_mem_paths [] t |>.2 ⟨u, htb, BTree.nil_mem_paths u⟩

theorem BTree.weight_eq_pathWeight_of_edgeValid (r : E → E → Prop) [DecidableRel r]
    (p : E → ℝ≥0∞) : ∀ {n : Nat} {a : E} (t : BTree E n a),
    t.EdgeValid r a → t.weight r p = t.pathWeight p a := by
  intro n
  induction n with
  | zero => intro a t; exact Fin.elim0 t
  | succ n ih =>
      intro a t hvalid
      rw [BTree.weight, BTree.pathWeight_succ]
      congr 1
      apply Finset.prod_congr rfl
      intro b _hb
      cases htb : t b with
      | none => simp [htb]
      | some u =>
          have hr : r a b := BTree.root_related_of_child htb hvalid
          simp only [htb, hr, if_pos]
          exact ih u (BTree.child_edgeValid htb hvalid)

structure ProperTree (r : E → E → Prop) (root : E) where
  paths : Finset (List E)
  root_mem : [] ∈ paths
  prefixClosed : PathsPrefixClosed paths
  edgeValid : ∀ ⦃q : List E⦄ ⦃b : E⦄,
    q ++ [b] ∈ paths → r (pathLabel root q) b
  stronglyProper : ∀ ⦃p q : List E⦄, p ∈ paths → q ∈ paths →
    p.length = q.length → r (pathLabel root p) (pathLabel root q) → p = q

@[ext]
theorem ProperTree.ext {r : E → E → Prop} {root : E}
    {s t : ProperTree r root} (h : s.paths = t.paths) : s = t := by
  cases s
  cases t
  simp_all

noncomputable instance ProperTree.instDecidableEq {r : E → E → Prop} {root : E} :
    DecidableEq (ProperTree r root) := Classical.decEq _

noncomputable instance ProperTree.instCountable {r : E → E → Prop} {root : E} :
    Countable (ProperTree r root) :=
  (show Function.Injective (@ProperTree.paths E r root) from
    fun _s _t h ↦ ProperTree.ext h).countable

noncomputable def ProperTree.weight {r : E → E → Prop} {root : E}
    (p : E → ℝ≥0∞) (t : ProperTree r root) : ℝ≥0∞ :=
  ∏ q ∈ t.paths, p (pathLabel root q)

noncomputable def historyTree (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    ProperTree r root where
  paths := (buildTimedTree r root history).paths
  root_mem := (buildTimedTree_good r hrefl hsymm root history).paths_root_mem
  prefixClosed := (buildTimedTree_good r hrefl hsymm root history).paths_prefixClosed
  edgeValid := (buildTimedTree_good r hrefl hsymm root history).paths_edgeValid
  stronglyProper :=
    (buildTimedTree_good r hrefl hsymm root history).paths_stronglyProper hsymm

def ProperTree.labelCount {r : E → E → Prop} {root : E}
    (label : E) (t : ProperTree r root) : Nat :=
  (t.paths.filter fun q ↦ pathLabel root q = label).card

theorem historyTree_root_labelCount (r : E → E → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (root : E) (history : List E) :
    (historyTree r hrefl hsymm root history).labelCount root = history.count root + 1 := by
  exact buildTimedTree_root_labelCount r hrefl hsymm root history

noncomputable def ProperTree.toBTree {r : E → E → Prop} {root : E}
    (t : ProperTree r root) (n : Nat) (hdepth : ∀ q ∈ t.paths, q.length < n + 1) :
    BTree E (n + 1) root :=
  Classical.choose <| BTree.exists_paths_eq n root t.paths t.root_mem hdepth t.prefixClosed

theorem ProperTree.toBTree_paths {r : E → E → Prop} {root : E}
    (t : ProperTree r root) (n : Nat) (hdepth : ∀ q ∈ t.paths, q.length < n + 1) :
    (t.toBTree n hdepth).paths = t.paths :=
  Classical.choose_spec <| BTree.exists_paths_eq n root t.paths t.root_mem hdepth t.prefixClosed

theorem ProperTree.toBTree_edgeValid {r : E → E → Prop} {root : E}
    (t : ProperTree r root) (n : Nat) (hdepth : ∀ q ∈ t.paths, q.length < n + 1) :
    (t.toBTree n hdepth).EdgeValid r root := by
  intro q b hqb
  rw [t.toBTree_paths n hdepth] at hqb
  exact t.edgeValid hqb

theorem ProperTree.toBTree_weight {r : E → E → Prop} [DecidableRel r]
    {root : E} (p : E → ℝ≥0∞) (t : ProperTree r root) (n : Nat)
    (hdepth : ∀ q ∈ t.paths, q.length < n + 1) :
    (t.toBTree n hdepth).weight r p = t.weight p := by
  rw [BTree.weight_eq_pathWeight_of_edgeValid r p _
    (t.toBTree_edgeValid n hdepth), BTree.pathWeight, ProperTree.weight,
    t.toBTree_paths n hdepth]

theorem ProperTree.tsum_weight_le_of_charge (r : E → E → Prop) [DecidableRel r]
    (p y : E → ℝ≥0∞)
    (hcharge : ∀ a, p a * ∏ b : E, (if r a b then 1 + y b else 1) ≤ y a)
    (root : E) :
    ∑' t : ProperTree r root, t.weight p ≤ y root := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S ↦ ?_
  let n := S.sup fun t ↦ t.paths.sup List.length
  have hdepth (t : ProperTree r root) (ht : t ∈ S) :
      ∀ q ∈ t.paths, q.length < n + 1 := by
    intro q hq
    apply Nat.lt_succ_of_le
    change q.length ≤ S.sup fun t ↦ t.paths.sup List.length
    exact (Finset.le_sup (f := List.length) hq).trans
      (Finset.le_sup (f := fun t : ProperTree r root ↦ t.paths.sup List.length) ht)
  let encode (t : ProperTree r root) : BTree E (n + 1) root :=
    if ht : t ∈ S then t.toBTree n (hdepth t ht) else fun _ ↦ none
  have hencode_paths (t : ProperTree r root) (ht : t ∈ S) :
      (encode t).paths = t.paths := by
    simp only [encode, dif_pos ht]
    exact t.toBTree_paths n (hdepth t ht)
  have hencode_inj : Set.InjOn encode (↑S : Set (ProperTree r root)) := by
    intro s hs t ht heq
    apply ProperTree.ext
    rw [← hencode_paths s hs, ← hencode_paths t ht, heq]
  calc
    ∑ t ∈ S, t.weight p = ∑ t ∈ S, (encode t).weight r p := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [show encode t = t.toBTree n (hdepth t ht) by simp [encode, ht]]
      exact (t.toBTree_weight p n (hdepth t ht)).symm
    _ = ∑ u ∈ S.image encode, u.weight r p := by
      rw [Finset.sum_image hencode_inj]
    _ ≤ ∑ u : BTree E (n + 1) root, u.weight r p := by
      apply Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ y root := BTree.sum_weight_le_of_charge r p y hcharge (n + 1) root

section Resampling

variable {I : Type} [Fintype I] [DecidableEq I]

theorem scopeRelated_refl (scope : E → Finset I) : Reflexive (scopeRelated scope) :=
  fun a ↦ Or.inl rfl

theorem scopeRelated_symm (scope : E → Finset I) : Symmetric (scopeRelated scope) := by
  intro a b hab
  rcases hab with hab | hab
  · exact Or.inl hab.symm
  · exact Or.inr fun h ↦ hab h.symm

abbrev ProperTree.Node {r : E → E → Prop} {root : E} (t : ProperTree r root) :=
  {q : List E // q ∈ t.paths}

def ProperTree.nodeLabel {r : E → E → Prop} {root : E}
    (t : ProperTree r root) (v : t.Node) : E :=
  pathLabel root v.1

abbrev ProperTree.Cell (scope : E → Finset I) {r : E → E → Prop} {root : E}
    (t : ProperTree r root) :=
  (v : t.Node) × {i : I // i ∈ scope (t.nodeLabel v)}

def ProperTree.deeperPaths (scope : E → Finset I) {r : E → E → Prop}
    {root : E} (t : ProperTree r root) (q : List E) (i : I) : Finset (List E) :=
  t.paths.filter fun p ↦ q.length < p.length ∧ i ∈ scope (pathLabel root p)

def ProperTree.sampleNumber (scope : E → Finset I) {r : E → E → Prop}
    {root : E} (t : ProperTree r root) (q : List E) (i : I) : Nat :=
  (t.deeperPaths scope q i).card

def ProperTree.cellIndex (scope : E → Finset I)
    {root : E} (t : ProperTree (scopeRelated scope) root) (c : t.Cell scope) :
    (i : I) × Nat :=
  ⟨c.2.1, t.sampleNumber scope c.1.1 c.2.1⟩

theorem ProperTree.sampleNumber_lt_of_length_lt (scope : E → Finset I)
    {root : E} (t : ProperTree (scopeRelated scope) root) {p q : List E} {i : I}
    (hp : p ∈ t.paths) (hq : q ∈ t.paths) (hip : i ∈ scope (pathLabel root p))
    (hiq : i ∈ scope (pathLabel root q)) (hlength : p.length < q.length) :
    t.sampleNumber scope q i < t.sampleNumber scope p i := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨q, ?_, ?_⟩
  · simp [ProperTree.deeperPaths]
  · intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simp [ProperTree.deeperPaths, hq, hiq, hlength]
    ·
      simp only [ProperTree.deeperPaths, Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hlength.trans hz.2.1, hz.2.2⟩

theorem ProperTree.cellIndex_injective (scope : E → Finset I) {root : E}
    (t : ProperTree (scopeRelated scope) root) :
    Function.Injective (t.cellIndex scope) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ heq
  have hij : i.1 = j.1 := congrArg Sigma.fst heq
  have hnum : t.sampleNumber scope p.1 i.1 = t.sampleNumber scope q.1 j.1 :=
    congrArg Sigma.snd heq
  have hnum' : t.sampleNumber scope p.1 i.1 = t.sampleNumber scope q.1 i.1 := by
    simpa only [← hij] using hnum
  have hi : i.1 ∈ scope (pathLabel root p.1) := i.2
  have hj : j.1 ∈ scope (pathLabel root q.1) := j.2
  have hlength : p.1.length = q.1.length := by
    rcases lt_trichotomy p.1.length q.1.length with hpq | hpq | hpq
    · have hlt := t.sampleNumber_lt_of_length_lt scope p.2 q.2 hi
        (by simpa [← hij] using hj) hpq
      omega
    · exact hpq
    · have hlt := t.sampleNumber_lt_of_length_lt scope q.2 p.2
        (by simpa [← hij] using hj) hi hpq
      omega
  have hrelated : scopeRelated scope (pathLabel root p.1) (pathLabel root q.1) := by
    apply Or.inr
    rw [Finset.not_disjoint_iff]
    exact ⟨i.1, hi, by simpa [← hij] using hj⟩
  have hpq : p.1 = q.1 := t.stronglyProper p.2 q.2 hlength hrelated
  have hpq_node : p = q := Subtype.ext hpq
  subst q
  have hij_sub : i = j := Subtype.ext hij
  subst j
  rfl

variable (Value : I → Type) [∀ i, MeasurableSpace (Value i)]

abbrev ProperTree.CellValues (scope : E → Finset I) {root : E}
    (t : ProperTree (scopeRelated scope) root) :=
  (c : t.Cell scope) → Value c.2.1

abbrev ProperTree.NodeValues (scope : E → Finset I) {root : E}
    (t : ProperTree (scopeRelated scope) root) :=
  (v : t.Node) → LocalAssignment Value (scope (t.nodeLabel v))

def ProperTree.extractCells (scope : E → Finset I) {root : E}
    (t : ProperTree (scopeRelated scope) root) (table : ResamplingTable Value) :
    t.CellValues Value scope :=
  fun c ↦ table (t.cellIndex scope c)

def ProperTree.groupedBad (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e))) {root : E}
    (t : ProperTree (scopeRelated scope) root) : Set (t.NodeValues Value scope) :=
  Set.pi (↑(Finset.univ : Finset t.Node)) fun v ↦ bad (t.nodeLabel v)

def ProperTree.curryCells (scope : E → Finset I) {root : E}
    (t : ProperTree (scopeRelated scope) root) :
    t.CellValues Value scope ≃ᵐ t.NodeValues Value scope :=
  MeasurableEquiv.piCurry fun (v : t.Node) (i : scope (t.nodeLabel v)) ↦ Value i.1

def ProperTree.cellBad (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e))) {root : E}
    (t : ProperTree (scopeRelated scope) root) : Set (t.CellValues Value scope) :=
  t.curryCells Value scope ⁻¹' t.groupedBad Value scope bad

def ProperTree.passes (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e))) {root : E}
    (t : ProperTree (scopeRelated scope) root) : Set (ResamplingTable Value) :=
  t.extractCells Value scope ⁻¹' t.cellBad Value scope bad

theorem ProperTree.mem_passes_iff (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e))) {root : E}
    (t : ProperTree (scopeRelated scope) root) (table : ResamplingTable Value) :
    table ∈ t.passes Value scope bad ↔
      ∀ v : t.Node,
        (fun i : scope (t.nodeLabel v) ↦
          table ⟨i.1, t.sampleNumber scope v.1 i.1⟩) ∈ bad (t.nodeLabel v) := by
  simp only [ProperTree.passes, ProperTree.cellBad, ProperTree.extractCells,
    ProperTree.groupedBad, Set.mem_preimage, Set.mem_pi]
  constructor
  · intro h v
    have hv := h v (by simp)
    simpa [ProperTree.curryCells, ProperTree.extractCells,
      ProperTree.cellIndex] using hv
  · intro h v _hv
    simpa [ProperTree.curryCells, ProperTree.extractCells,
      ProperTree.cellIndex] using h v

theorem ProperTree.measurableSet_groupedBad (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) {root : E}
    (t : ProperTree (scopeRelated scope) root) :
    MeasurableSet (t.groupedBad Value scope bad) := by
  rw [ProperTree.groupedBad, Finset.coe_univ]
  apply MeasurableSet.pi Set.countable_univ
  intro v _hv
  exact hbad (t.nodeLabel v)

theorem ProperTree.measurableSet_cellBad (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) {root : E}
    (t : ProperTree (scopeRelated scope) root) :
    MeasurableSet (t.cellBad Value scope bad) :=
  (t.measurableSet_groupedBad Value scope bad hbad).preimage (by fun_prop)

theorem ProperTree.measurableSet_passes (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) {root : E}
    (t : ProperTree (scopeRelated scope) root) :
    MeasurableSet (t.passes Value scope bad) := by
  apply (t.measurableSet_cellBad Value scope bad hbad).preimage
  change Measurable (fun (table : ResamplingTable Value) (c : t.Cell scope) ↦
    table (t.cellIndex scope c))
  fun_prop

theorem ProperTree.measure_passes (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) {root : E}
    (t : ProperTree (scopeRelated scope) root) :
    tableMeasure Value μ (t.passes Value scope bad) =
      t.weight (eventProbability Value μ scope bad) := by
  have hmap :
      (MeasureTheory.Measure.infinitePi
          (fun j : TableIndex (I := I) ↦ μ j.1)).map (t.extractCells Value scope) =
        MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1) := by
    change (MeasureTheory.Measure.infinitePi
        (fun j : TableIndex (I := I) ↦ μ j.1)).map
        (fun table c ↦ table (t.cellIndex scope c)) = _
    exact MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
      (t.cellIndex_injective scope)
  have hextractMeas : Measurable (t.extractCells Value scope) := by
    change Measurable (fun (table : ResamplingTable Value) (c : t.Cell scope) ↦
      table (t.cellIndex scope c))
    fun_prop
  have hcurryMap :
      (MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1)).map
          (t.curryCells Value scope) =
        MeasureTheory.Measure.infinitePi (fun v : t.Node ↦
          MeasureTheory.Measure.infinitePi
            (fun i : scope (t.nodeLabel v) ↦ μ i.1)) := by
    change (MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1)).map
        (MeasurableEquiv.piCurry
          fun (v : t.Node) (i : scope (t.nodeLabel v)) ↦ Value i.1) = _
    exact MeasureTheory.Measure.infinitePi_map_piCurry
      (fun (v : t.Node) (i : scope (t.nodeLabel v)) ↦ μ i.1)
  have hcell :
      MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1)
          (t.cellBad Value scope bad) =
        t.weight (eventProbability Value μ scope bad) := by
    calc
      MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1)
          (t.cellBad Value scope bad) =
          (MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1)).map
            (t.curryCells Value scope) (t.groupedBad Value scope bad) := by
        exact (MeasureTheory.Measure.map_apply (by fun_prop)
          (t.measurableSet_groupedBad Value scope bad hbad)).symm
      _ = MeasureTheory.Measure.infinitePi (fun v : t.Node ↦
            MeasureTheory.Measure.infinitePi
              (fun i : scope (t.nodeLabel v) ↦ μ i.1))
            (t.groupedBad Value scope bad) :=
        congrArg (fun m ↦ m (t.groupedBad Value scope bad)) hcurryMap
      _ = ∏ v : t.Node,
            localMeasure Value μ (scope (t.nodeLabel v))
              (bad (t.nodeLabel v)) := by
        have hpi := MeasureTheory.Measure.infinitePi_pi
          (μ := fun v : t.Node ↦ MeasureTheory.Measure.infinitePi
            (fun i : scope (t.nodeLabel v) ↦ μ i.1))
          (s := (Finset.univ : Finset t.Node))
          (t := fun v ↦ bad (t.nodeLabel v))
          (fun v _hv ↦ hbad (t.nodeLabel v))
        simpa only [ProperTree.groupedBad, localMeasure] using hpi
      _ = t.weight (eventProbability Value μ scope bad) := by
        rw [ProperTree.weight]
        change (∏ v : t.Node,
            eventProbability Value μ scope bad (pathLabel root v.1)) =
          ∏ q ∈ t.paths,
            eventProbability Value μ scope bad (pathLabel root q)
        rw [Finset.univ_eq_attach]
        exact Finset.prod_attach t.paths
          (fun q ↦ eventProbability Value μ scope bad (pathLabel root q))
  calc
    tableMeasure Value μ (t.passes Value scope bad) =
        (tableMeasure Value μ).map (t.extractCells Value scope)
          (t.cellBad Value scope bad) := by
      simpa only [ProperTree.passes] using
        (MeasureTheory.Measure.map_apply
          hextractMeas
          (t.measurableSet_cellBad Value scope bad hbad)).symm
    _ = MeasureTheory.Measure.infinitePi (fun c : t.Cell scope ↦ μ c.2.1)
          (t.cellBad Value scope bad) := by
      rw [tableMeasure]
      exact congrArg (fun m ↦ m (t.cellBad Value scope bad)) hmap
    _ = t.weight (eventProbability Value μ scope bad) := hcell

noncomputable def priorCountFor (scope : E → Finset I) (log : Nat → Option E)
    (k : Nat) (i : I) : Nat := by
  classical
  exact ((Finset.range k).filter fun l ↦ match log l with
    | none => False
    | some e => i ∈ scope e).card

theorem buildTimedTree_priorCount_eq_sampleNumber (scope : E → Finset I)
    (root : E) (history : List E) (log : Nat → Option E)
    (hlog : ∀ k < history.length, history[k]? = log k)
    {kp : Nat × List E}
    (hkp : kp ∈ buildTimedTree (scopeRelated scope) root history) {i : I}
    (hi : i ∈ scope (pathLabel root kp.2)) :
    priorCountFor scope log kp.1 i =
      (historyTree (scopeRelated scope) (scopeRelated_refl scope)
        (scopeRelated_symm scope) root history).sampleNumber scope kp.2 i := by
  classical
  let state := buildTimedTree (scopeRelated scope) root history
  let good := buildTimedTree_good (scopeRelated scope) (scopeRelated_refl scope)
    (scopeRelated_symm scope) root history
  have hk_le : kp.1 ≤ history.length := by
    rcases good.represents hkp with hrep | hroot
    · apply Nat.le_of_lt
      by_contra hnot
      have hnone : history[kp.1]? = none :=
        List.getElem?_eq_none (Nat.le_of_not_gt hnot)
      rw [hrep] at hnone
      simp at hnone
    · exact hroot.1.le
  let source := (Finset.range kp.1).filter fun l ↦ match log l with
    | none => False
    | some e => i ∈ scope e
  let target := (buildTimedTree (scopeRelated scope) root history).paths.filter fun q ↦
    kp.2.length < q.length ∧ i ∈ scope (pathLabel root q)
  have source_data (l : Nat) (hl : l ∈ source) :
      ∃ e, log l = some e ∧ i ∈ scope e ∧ l < kp.1 := by
    have hl' := Finset.mem_filter.mp hl
    have hlt := Finset.mem_range.mp hl'.1
    cases hlogl : log l with
    | none => simp [source, hlogl] at hl
    | some e =>
        exact ⟨e, rfl, by simpa [source, hlogl] using hl'.2, hlt⟩
  have path_exists (l : Nat) (hl : l ∈ source) :
      ∃ q, (l, q) ∈ state := by
    obtain ⟨e, hlogl, hie, hlt⟩ := source_data l hl
    have hlhist : l < history.length := hlt.trans_le hk_le
    have hentry : history[l]? = some e := by rw [hlog l hlhist, hlogl]
    have hrelated : scopeRelated scope e (pathLabel root kp.2) := by
      apply Or.inr
      rw [Finset.not_disjoint_iff]
      exact ⟨i, hie, hi⟩
    exact good.closed hkp hentry hlt hrelated
  let pathOf (l : Nat) (hl : l ∈ source) : List E := Classical.choose (path_exists l hl)
  have pathOf_mem (l : Nat) (hl : l ∈ source) : (l, pathOf l hl) ∈ state :=
    Classical.choose_spec (path_exists l hl)
  have pathOf_target (l : Nat) (hl : l ∈ source) : pathOf l hl ∈ target := by
    obtain ⟨e, hlogl, hie, hlt⟩ := source_data l hl
    have hlhist : l < history.length := hlt.trans_le hk_le
    have hentry : history[l]? = some e := by rw [hlog l hlhist, hlogl]
    have hlabel : pathLabel root (pathOf l hl) = e := by
      rcases good.represents (pathOf_mem l hl) with hrep | hroot
      · rw [hentry] at hrep
        exact (Option.some.inj hrep).symm
      · omega
    have hrelated : scopeRelated scope (pathLabel root (pathOf l hl))
        (pathLabel root kp.2) := by
      rw [hlabel]
      apply Or.inr
      rw [Finset.not_disjoint_iff]
      exact ⟨i, hie, hi⟩
    have hdepth := good.chronological (pathOf_mem l hl) hkp hlt hrelated
    exact Finset.mem_filter.mpr ⟨TimedTree.mem_paths.mpr ⟨l, pathOf_mem l hl⟩,
      hdepth, by simpa [hlabel] using hie⟩
  have pathOf_inj (l₁ : Nat) (hl₁ : l₁ ∈ source) (l₂ : Nat) (hl₂ : l₂ ∈ source)
      (heq : pathOf l₁ hl₁ = pathOf l₂ hl₂) : l₁ = l₂ := by
    have hpairs := good.pathsUnique (pathOf_mem l₁ hl₁) (pathOf_mem l₂ hl₂) heq
    exact congrArg Prod.fst hpairs
  have pathOf_surj (q : List E) (hq : q ∈ target) :
      ∃ l hl, pathOf l hl = q := by
    have hq' := Finset.mem_filter.mp hq
    obtain ⟨l, hl⟩ := TimedTree.mem_paths.mp hq'.1
    have hrelated : scopeRelated scope (pathLabel root kp.2) (pathLabel root q) := by
      apply Or.inr
      rw [Finset.not_disjoint_iff]
      exact ⟨i, hi, hq'.2.2⟩
    have hlt : l < kp.1 := by
      rcases lt_trichotomy l kp.1 with hlk | hlk | hlk
      · exact hlk
      · have hpairs := good.timesUnique hl hkp hlk
        have hpq : q = kp.2 := congrArg Prod.snd hpairs
        have hdepth := hq'.2.1
        rw [hpq] at hdepth
        omega
      · have hcontra := good.chronological hkp hl hlk hrelated
        change q.length < kp.2.length at hcontra
        omega
    have hlhist : l < history.length := hlt.trans_le hk_le
    have hlabel : history[l]? = some (pathLabel root q) := by
      rcases good.represents hl with hrep | hroot
      · exact hrep
      · omega
    have hlogl : log l = some (pathLabel root q) := by
      rw [← hlog l hlhist]
      exact hlabel
    have hlsource : l ∈ source := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hlt, by simp [hlogl, hq'.2.2]⟩
    refine ⟨l, hlsource, ?_⟩
    have hpairs := good.timesUnique (pathOf_mem l hlsource) hl rfl
    exact congrArg Prod.snd hpairs
  have hcard : source.card = target.card :=
    Finset.card_bij pathOf pathOf_target pathOf_inj pathOf_surj
  simpa [priorCountFor, source, target, ProperTree.sampleNumber,
    ProperTree.deeperPaths, historyTree] using hcard

theorem runCounts_succ (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value) (n : Nat) :
    runCounts Value scope bad rule table (n + 1) =
      advanceCounts scope (runCounts Value scope bad rule table n)
        (resamplingLog Value scope bad rule table n) := by
  rfl

theorem runCounts_eq_priorCount (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value) :
    ∀ (n : Nat) (i : I),
      runCounts Value scope bad rule table n i =
        priorCountFor scope (resamplingLog Value scope bad rule table) n i := by
  classical
  intro n
  induction n with
  | zero => simp [runCounts, priorCountFor]
  | succ n ih =>
      intro i
      rw [runCounts_succ]
      unfold priorCountFor at ih ⊢
      rw [Finset.range_add_one, Finset.filter_insert]
      have hnnot : n ∉ (Finset.range n).filter fun l ↦
          match resamplingLog Value scope bad rule table l with
          | none => False
          | some e => i ∈ scope e := by simp
      cases hlog : resamplingLog Value scope bad rule table n with
      | none =>
          simp [advanceCounts, hlog, ih]
      | some e =>
          by_cases hie : i ∈ scope e
          · simp [advanceCounts, hlog, hie, Finset.card_insert_of_notMem hnnot, ih]
          · simp [advanceCounts, hlog, hie, ih]

theorem resamplingLog_succ_eq_none_of_eq_none (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value) {n : Nat}
    (h : resamplingLog Value scope bad rule table n = none) :
    resamplingLog Value scope bad rule table (n + 1) = none := by
  rw [resamplingLog, runCounts_succ]
  change rule.choose (currentAssignment Value table
    (advanceCounts scope (runCounts Value scope bad rule table n)
      (resamplingLog Value scope bad rule table n))) = none
  rw [h]
  exact h

theorem resamplingLog_eq_none_of_le (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    {n m : Nat} (hnm : n ≤ m)
    (h : resamplingLog Value scope bad rule table n = none) :
    resamplingLog Value scope bad rule table m = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => simpa
  | succ d ih =>
      rw [Nat.add_succ]
      exact resamplingLog_succ_eq_none_of_eq_none Value scope bad rule table ih

def executionHistory (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) (t : Nat) : List E :=
  List.ofFn fun k : Fin t ↦ (resamplingLog Value scope bad rule table k).getD root

@[simp]
theorem executionHistory_length (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) (t : Nat) :
    (executionHistory Value scope bad rule table root t).length = t := by
  simp [executionHistory]

theorem resamplingLog_eq_some_of_lt_of_some (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    {root : E} {t k : Nat}
    (ht : resamplingLog Value scope bad rule table t = some root) (hk : k < t) :
    ∃ e, resamplingLog Value scope bad rule table k = some e := by
  cases hlogk : resamplingLog Value scope bad rule table k with
  | some e => exact ⟨e, rfl⟩
  | none =>
      have := resamplingLog_eq_none_of_le Value scope bad rule table (Nat.le_of_lt hk) hlogk
      rw [ht] at this
      simp at this

theorem executionHistory_getElem?_eq_log (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    {root : E} {t k : Nat}
    (ht : resamplingLog Value scope bad rule table t = some root) (hk : k < t) :
    (executionHistory Value scope bad rule table root t)[k]? =
      resamplingLog Value scope bad rule table k := by
  obtain ⟨e, he⟩ := resamplingLog_eq_some_of_lt_of_some Value scope bad rule table ht hk
  rw [he]
  simp [executionHistory, hk]
  simp [he]

theorem historyTree_passes_of_resamplingLog_eq_some (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    {root : E} {t : Nat}
    (ht : resamplingLog Value scope bad rule table t = some root) :
    table ∈ (historyTree (scopeRelated scope) (scopeRelated_refl scope)
      (scopeRelated_symm scope) root
      (executionHistory Value scope bad rule table root t)).passes Value scope bad := by
  classical
  rw [ProperTree.mem_passes_iff]
  intro v
  let history := executionHistory Value scope bad rule table root t
  have hhistory_log : ∀ k < history.length,
      history[k]? = resamplingLog Value scope bad rule table k := by
    intro k hk
    apply executionHistory_getElem?_eq_log Value scope bad rule table ht
    simpa [history] using hk
  have hvpath : v.1 ∈ (buildTimedTree (scopeRelated scope) root history).paths := v.2
  obtain ⟨k, hkv⟩ := TimedTree.mem_paths.mp hvpath
  have hklog : resamplingLog Value scope bad rule table k =
      some (pathLabel root v.1) := by
    let good := buildTimedTree_good (scopeRelated scope) (scopeRelated_refl scope)
      (scopeRelated_symm scope) root history
    rcases good.represents hkv with hrep | hroot
    · have hklt : k < history.length := by
        by_contra hnot
        have hnone : history[k]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_gt hnot)
        rw [hrep] at hnone
        simp at hnone
      rw [← hhistory_log k hklt]
      exact hrep
    · have hkt : k = t := by simpa [history] using hroot.1
      have hvnil : v.1 = [] := by simpa using hroot.2
      rw [hkt, hvnil]
      exact ht
  have hviolate := rule.sound hklog
  have hcount (i : scope (pathLabel root v.1)) :
      runCounts Value scope bad rule table k i.1 =
        (historyTree (scopeRelated scope) (scopeRelated_refl scope)
          (scopeRelated_symm scope) root history).sampleNumber scope v.1 i.1 := by
    rw [runCounts_eq_priorCount]
    exact buildTimedTree_priorCount_eq_sampleNumber scope root history
      (resamplingLog Value scope bad rule table) hhistory_log hkv i.2
  change (fun i : scope (pathLabel root v.1) ↦
    table ⟨i.1, (historyTree (scopeRelated scope) (scopeRelated_refl scope)
      (scopeRelated_symm scope) root history).sampleNumber scope v.1 i.1⟩) ∈
        bad (pathLabel root v.1)
  change restrictAssignment Value scope
    (currentAssignment Value table (runCounts Value scope bad rule table k))
      (pathLabel root v.1) ∈ bad (pathLabel root v.1) at hviolate
  convert hviolate using 1
  funext i
  simp only [restrictAssignment, currentAssignment]
  rw [hcount i]

theorem executionHistory_succ (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) (t : Nat) :
    executionHistory Value scope bad rule table root (t + 1) =
      executionHistory Value scope bad rule table root t ++
        [(resamplingLog Value scope bad rule table t).getD root] := by
  unfold executionHistory
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, Fin.coe_castSucc, Fin.val_last]

theorem executionHistory_count_mono (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) {t u : Nat} (htu : t ≤ u) :
    (executionHistory Value scope bad rule table root t).count root ≤
      (executionHistory Value scope bad rule table root u).count root := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, executionHistory_succ, List.count_append]
      omega

theorem executionHistory_count_lt_of_log_eq_some (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    {root : E} {t u : Nat} (htu : t < u)
    (ht : resamplingLog Value scope bad rule table t = some root) :
    (executionHistory Value scope bad rule table root t).count root <
      (executionHistory Value scope bad rule table root u).count root := by
  have hstep :
      (executionHistory Value scope bad rule table root t).count root <
        (executionHistory Value scope bad rule table root (t + 1)).count root := by
    rw [executionHistory_succ, List.count_append]
    simp [ht]
  exact hstep.trans_le <| executionHistory_count_mono Value scope bad rule table root
    (Nat.succ_le_iff.mpr htu)

noncomputable def occurrenceTree (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) (t : Nat) : ProperTree (scopeRelated scope) root :=
  historyTree (scopeRelated scope) (scopeRelated_refl scope)
    (scopeRelated_symm scope) root
    (executionHistory Value scope bad rule table root t)

theorem occurrenceTree_injectiveOn (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) :
    Set.InjOn (occurrenceTree Value scope bad rule table root)
      {t | resamplingLog Value scope bad rule table t = some root} := by
  intro t ht u hu heq
  rcases lt_trichotomy t u with htu | htu | htu
  · exfalso
    have hcount := executionHistory_count_lt_of_log_eq_some Value scope bad rule table
      htu ht
    have hlabels := congrArg (ProperTree.labelCount root) heq
    simp only [occurrenceTree, historyTree_root_labelCount] at hlabels
    omega
  · exact htu
  · exfalso
    have hcount := executionHistory_count_lt_of_log_eq_some Value scope bad rule table
      htu hu
    have hlabels := congrArg (ProperTree.labelCount root) heq
    simp only [occurrenceTree, historyTree_root_labelCount] at hlabels
    omega

noncomputable def passingTreeCount (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (table : ResamplingTable Value) (root : E) : ℝ≥0∞ :=
  ∑' tree : ProperTree (scopeRelated scope) root,
    Set.indicator (tree.passes Value scope bad) (fun _ ↦ (1 : ℝ≥0∞)) table

theorem resamplingCount_le_passingTreeCount (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) :
    resamplingCount Value scope bad rule table root ≤
      passingTreeCount Value scope bad table root := by
  classical
  let times : Set Nat :=
    {t | resamplingLog Value scope bad rule table t = some root}
  let treeOf (t : times) : ProperTree (scopeRelated scope) root :=
    occurrenceTree Value scope bad rule table root t.1
  have hinj : Function.Injective treeOf := by
    intro t u htu
    apply Subtype.ext
    exact occurrenceTree_injectiveOn Value scope bad rule table root t.2 u.2 htu
  have hpass (t : times) : table ∈ (treeOf t).passes Value scope bad := by
    exact historyTree_passes_of_resamplingLog_eq_some Value scope bad rule table t.2
  calc
    resamplingCount Value scope bad rule table root =
        ∑' t : times, (1 : ℝ≥0∞) := by
      rw [resamplingCount]
      change (∑' t : Nat, times.indicator (fun _ ↦ (1 : ℝ≥0∞)) t) = _
      exact (tsum_subtype times (fun _ ↦ (1 : ℝ≥0∞))).symm
    _ = ∑' t : times,
        Set.indicator ((treeOf t).passes Value scope bad)
          (fun _ ↦ (1 : ℝ≥0∞)) table := by
      apply tsum_congr
      intro t
      rw [Set.indicator_of_mem (hpass t)]
    _ ≤ ∑' tree : ProperTree (scopeRelated scope) root,
        Set.indicator (tree.passes Value scope bad)
          (fun _ ↦ (1 : ℝ≥0∞)) table :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj _
    _ = passingTreeCount Value scope bad table root := rfl

theorem expectedResamplings_le_of_charge
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : SelectionRule Value scope bad) (y : E → ℝ≥0∞)
    (hcharge : ∀ a,
      eventProbability Value μ scope bad a *
        ∏ b : E, (if scopeRelated scope a b then 1 + y b else 1) ≤ y a)
    (root : E) :
    expectedResamplings Value μ scope bad rule root ≤ y root := by
  calc
    expectedResamplings Value μ scope bad rule root ≤
        ∫⁻ table, passingTreeCount Value scope bad table root
          ∂tableMeasure Value μ := by
      apply MeasureTheory.lintegral_mono
      intro table
      exact resamplingCount_le_passingTreeCount Value scope bad rule table root
    _ = ∑' tree : ProperTree (scopeRelated scope) root,
        tree.weight (eventProbability Value μ scope bad) := by
      change (∫⁻ table, ∑' tree : ProperTree (scopeRelated scope) root,
        Set.indicator (tree.passes Value scope bad)
          (fun _ ↦ (1 : ℝ≥0∞)) table ∂tableMeasure Value μ) = _
      rw [MeasureTheory.lintegral_tsum]
      · apply tsum_congr
        intro tree
        have hpasses := tree.measurableSet_passes Value scope bad hbad
        rw [MeasureTheory.lintegral_indicator hpasses]
        simp only [MeasureTheory.lintegral_const, one_mul,
          MeasureTheory.Measure.restrict_apply_univ]
        exact tree.measure_passes Value μ scope bad hbad
      · intro tree
        exact (measurable_const.indicator
          (tree.measurableSet_passes Value scope bad hbad)).aemeasurable
    _ ≤ y root := ProperTree.tsum_weight_le_of_charge
      (scopeRelated scope) (eventProbability Value μ scope bad) y hcharge root

theorem one_sub_mul_one_add_odds (x : E → NNReal)
    (hx : ∀ a, x a < 1) (a : E) :
    (1 - x a) * (1 + odds x a) = 1 := by
  apply NNReal.eq
  have hxr : (x a : ℝ) < 1 := by exact_mod_cast hx a
  simp only [NNReal.coe_mul, NNReal.coe_sub (hx a).le, NNReal.coe_one,
    NNReal.coe_add, NNReal.coe_div, odds]
  field_simp [show (1 : ℝ) - x a ≠ 0 by linarith]
  linarith

theorem mul_one_add_odds (x : E → NNReal)
    (hx : ∀ a, x a < 1) (a : E) :
    x a * (1 + odds x a) = odds x a := by
  apply NNReal.eq
  have hxr : (x a : ℝ) < 1 := by exact_mod_cast hx a
  simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_sub (hx a).le, odds]
  field_simp [show (1 : ℝ) - x a ≠ 0 by linarith]
  ring

noncomputable def oddsFactor (scope : E → Finset I) (x : E → NNReal)
    (a b : E) : NNReal :=
  if scopeRelated scope a b then 1 + odds x b else 1

theorem localLemmaFactor_mul_oddsFactor (scope : E → Finset I)
    (x : E → NNReal) (hx : ∀ a, x a < 1) (a b : E) :
    localLemmaFactor scope x a b * oddsFactor scope x a b =
      if b = a then 1 + odds x a else 1 := by
  by_cases hba : b = a
  · subst b
    simp [localLemmaFactor, oddsFactor, scopeRelated]
  · by_cases hdis : Disjoint (scope a) (scope b)
    · simp [localLemmaFactor, oddsFactor, scopeRelated, hba, hdis,
        Ne.symm hba]
    · simp [localLemmaFactor, oddsFactor, scopeRelated, hba, hdis,
        Ne.symm hba, one_sub_mul_one_add_odds x hx b]

theorem localLemmaBound_mul_oddsProduct (scope : E → Finset I)
    (x : E → NNReal) (hx : ∀ a, x a < 1) (a : E) :
    localLemmaBound scope x a * ∏ b : E, oddsFactor scope x a b = odds x a := by
  rw [localLemmaBound]
  calc
    (x a * ∏ b : E, localLemmaFactor scope x a b) *
        ∏ b : E, oddsFactor scope x a b =
        x a * ((∏ b : E, localLemmaFactor scope x a b) *
          ∏ b : E, oddsFactor scope x a b) := by ac_rfl
    _ = x a * ∏ b : E,
        (localLemmaFactor scope x a b * oddsFactor scope x a b) := by
      rw [Finset.prod_mul_distrib]
    _ = x a * ∏ b : E, (if b = a then 1 + odds x a else 1) := by
      congr 1
      apply Finset.prod_congr rfl
      intro b _hb
      exact localLemmaFactor_mul_oddsFactor scope x hx a b
    _ = x a * (1 + odds x a) := by
      rw [Fintype.prod_ite_eq' a]
    _ = odds x a := mul_one_add_odds x hx a

theorem charge_of_localLemmaBound (scope : E → Finset I)
    (p : E → ℝ≥0∞) (x : E → NNReal) (hx : ∀ a, x a < 1)
    (hp : ∀ a, p a ≤ (localLemmaBound scope x a : ℝ≥0∞)) :
    ∀ a, p a * ∏ b : E,
        (if scopeRelated scope a b then 1 + (odds x b : ℝ≥0∞) else 1) ≤
      (odds x a : ℝ≥0∞) := by
  intro a
  calc
    p a * ∏ b : E,
        (if scopeRelated scope a b then 1 + (odds x b : ℝ≥0∞) else 1) ≤
        (localLemmaBound scope x a : ℝ≥0∞) *
          ∏ b : E,
            (if scopeRelated scope a b then 1 + (odds x b : ℝ≥0∞) else 1) :=
      mul_le_mul_right' (hp a) _
    _ = ((localLemmaBound scope x a *
          ∏ b : E, oddsFactor scope x a b : NNReal) : ℝ≥0∞) := by
      refine Eq.trans ?_ (ENNReal.coe_mul _ _).symm
      congr 1
      rw [ENNReal.coe_finset_prod]
      apply Finset.prod_congr rfl
      intro b _hb
      by_cases hr : scopeRelated scope a b
      · simp [oddsFactor, hr]
      · simp [oddsFactor, hr]
    _ = (odds x a : ℝ≥0∞) := by
      rw [localLemmaBound_mul_oddsProduct scope x hx a]

theorem expectedResamplings_le
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : SelectionRule Value scope bad) (x : E → NNReal)
    (hx : ∀ a, x a < 1)
    (hprob : ∀ a, eventProbability Value μ scope bad a ≤
      (localLemmaBound scope x a : ℝ≥0∞)) (root : E) :
    expectedResamplings Value μ scope bad rule root ≤
      (odds x root : ℝ≥0∞) := by
  apply expectedResamplings_le_of_charge Value μ scope bad hbad rule
    (fun a ↦ (odds x a : ℝ≥0∞))
  exact charge_of_localLemmaBound scope (eventProbability Value μ scope bad)
    x hx hprob

theorem expectedTotalResamplings_le
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : SelectionRule Value scope bad) (x : E → NNReal)
    (hx : ∀ a, x a < 1)
    (hprob : ∀ a, eventProbability Value μ scope bad a ≤
      (localLemmaBound scope x a : ℝ≥0∞)) :
    expectedTotalResamplings Value μ scope bad rule ≤
      ∑ e : E, (odds x e : ℝ≥0∞) := by
  apply Finset.sum_le_sum
  intro e _he
  exact expectedResamplings_le Value μ scope bad hbad rule x hx hprob e

theorem measurable_passingTreeCount (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) (root : E) :
    Measurable (passingTreeCount Value scope bad · root) := by
  unfold passingTreeCount
  apply Measurable.tsum
  intro tree
  exact measurable_const.indicator
    (tree.measurableSet_passes Value scope bad hbad)

theorem lintegral_passingTreeCount
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) (root : E) :
    (∫⁻ table, passingTreeCount Value scope bad table root
      ∂tableMeasure Value μ) =
      ∑' tree : ProperTree (scopeRelated scope) root,
        tree.weight (eventProbability Value μ scope bad) := by
  change (∫⁻ table, ∑' tree : ProperTree (scopeRelated scope) root,
    Set.indicator (tree.passes Value scope bad)
      (fun _ ↦ (1 : ℝ≥0∞)) table ∂tableMeasure Value μ) = _
  rw [MeasureTheory.lintegral_tsum]
  · apply tsum_congr
    intro tree
    have hpasses := tree.measurableSet_passes Value scope bad hbad
    rw [MeasureTheory.lintegral_indicator hpasses]
    simp only [MeasureTheory.lintegral_const, one_mul,
      MeasureTheory.Measure.restrict_apply_univ]
    exact tree.measure_passes Value μ scope bad hbad
  · intro tree
    exact (measurable_const.indicator
      (tree.measurableSet_passes Value scope bad hbad)).aemeasurable

theorem lintegral_passingTreeCount_le_of_charge
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) (y : E → ℝ≥0∞)
    (hcharge : ∀ a,
      eventProbability Value μ scope bad a *
        ∏ b : E, (if scopeRelated scope a b then 1 + y b else 1) ≤ y a)
    (root : E) :
    (∫⁻ table, passingTreeCount Value scope bad table root
      ∂tableMeasure Value μ) ≤ y root := by
  rw [lintegral_passingTreeCount Value μ scope bad hbad root]
  exact ProperTree.tsum_weight_le_of_charge
    (scopeRelated scope) (eventProbability Value μ scope bad) y hcharge root

theorem exists_table_passingTreeCount_lt_top
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e)) (y : E → ℝ≥0∞)
    (hy : ∀ e, y e < ⊤)
    (hcharge : ∀ a,
      eventProbability Value μ scope bad a *
        ∏ b : E, (if scopeRelated scope a b then 1 + y b else 1) ≤ y a) :
    ∃ table : ResamplingTable Value,
      ∀ e, passingTreeCount Value scope bad table e < ⊤ := by
  have hae : ∀ᵐ table ∂tableMeasure Value μ,
      ∀ e, passingTreeCount Value scope bad table e < ⊤ := by
    rw [Filter.eventually_all]
    intro e
    apply MeasureTheory.ae_lt_top
      (measurable_passingTreeCount Value scope bad hbad e)
    apply ne_of_lt
    exact (lintegral_passingTreeCount_le_of_charge Value μ scope bad hbad y
      hcharge e).trans_lt (hy e)
  letI : MeasureTheory.IsProbabilityMeasure (tableMeasure Value μ) := by
    unfold tableMeasure
    infer_instance
  letI : (MeasureTheory.ae (tableMeasure Value μ)).NeBot :=
    MeasureTheory.ae_neBot.mpr
      (MeasureTheory.IsProbabilityMeasure.ne_zero (tableMeasure Value μ))
  exact hae.exists

theorem resamplingTimes_finite_of_count_lt_top (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E)
    (hcount : resamplingCount Value scope bad rule table root < ⊤) :
    Set.Finite {t | resamplingLog Value scope bad rule table t = some root} := by
  classical
  let times : Set Nat :=
    {t | resamplingLog Value scope bad rule table t = some root}
  have hcount_eq : resamplingCount Value scope bad rule table root =
      ∑' _t : times, (1 : ℝ≥0∞) := by
    rw [resamplingCount]
    change (∑' t : Nat, times.indicator (fun _ ↦ (1 : ℝ≥0∞)) t) = _
    exact (tsum_subtype times (fun _ ↦ (1 : ℝ≥0∞))).symm
  change times.Finite
  by_contra hfinite
  letI : Infinite times := Set.Infinite.to_subtype hfinite
  have htop : (∑' _t : times, (1 : ℝ≥0∞)) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  rw [hcount_eq, htop] at hcount
  exact (lt_irrefl ⊤ hcount)

theorem exists_termination_time_of_passing_lt_top (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (hpass : ∀ e, passingTreeCount Value scope bad table e < ⊤) :
    ∃ t, resamplingLog Value scope bad rule table t = none := by
  classical
  let times (e : E) : Set Nat :=
    {t | resamplingLog Value scope bad rule table t = some e}
  have hfinite (e : E) : (times e).Finite := by
    apply resamplingTimes_finite_of_count_lt_top Value scope bad rule table e
    exact (resamplingCount_le_passingTreeCount Value scope bad rule table e).trans_lt
      (hpass e)
  have hall : (Set.iUnion times).Finite := Set.finite_iUnion hfinite
  obtain ⟨t, ht⟩ := hall.exists_notMem
  cases hlog : resamplingLog Value scope bad rule table t with
  | none => exact ⟨t, hlog⟩
  | some e =>
      exfalso
      apply ht
      exact Set.mem_iUnion.mpr ⟨e, hlog⟩

theorem exists_good_assignment_of_passing_lt_top (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (hpass : ∀ e, passingTreeCount Value scope bad table e < ⊤) :
    ∃ a : Assignment Value, ∀ e, ¬violates Value scope bad a e := by
  obtain ⟨t, ht⟩ := exists_termination_time_of_passing_lt_top
    Value scope bad rule table hpass
  exact ⟨currentAssignment Value table
    (runCounts Value scope bad rule table t), rule.complete ht⟩

theorem exists_good_assignment
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : SelectionRule Value scope bad) (x : E → NNReal)
    (hx : ∀ a, x a < 1)
    (hprob : ∀ a, eventProbability Value μ scope bad a ≤
      (localLemmaBound scope x a : ℝ≥0∞)) :
    ∃ a : Assignment Value, ∀ e, ¬violates Value scope bad a e := by
  have hcharge := charge_of_localLemmaBound scope
    (eventProbability Value μ scope bad) x hx hprob
  obtain ⟨table, htable⟩ := exists_table_passingTreeCount_lt_top
    Value μ scope bad hbad (fun e ↦ (odds x e : ℝ≥0∞))
    (fun e ↦ ENNReal.coe_lt_top) hcharge
  exact exists_good_assignment_of_passing_lt_top Value scope bad rule table htable

/--
---
conclusion: Lax41.MoserTardos.moser_tardos
---
The Moser--Tardos witness-tree argument.  An infinite table supplies every
fresh sample used by the algorithm.  Each resampling occurrence injects into
a proper witness tree, the probability that a fixed tree occurs is the
product of its event probabilities, and the branching-process estimate sums
these products.  Finiteness of that sum also yields a terminating table and
hence an assignment avoiding all bad events.
-/
theorem moser_tardos
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : SelectionRule Value scope bad) (x : E → NNReal)
    (_hx_pos : ∀ a, 0 < x a) (hx_lt_one : ∀ a, x a < 1)
    (hprob : ∀ a, eventProbability Value μ scope bad a ≤
      (localLemmaBound scope x a : ℝ≥0∞)) :
    (∃ a : Assignment Value, ∀ e, ¬violates Value scope bad a e) ∧
      (∀ root, expectedResamplings Value μ scope bad rule root ≤
        (odds x root : ℝ≥0∞)) ∧
      expectedTotalResamplings Value μ scope bad rule ≤
        ∑ e : E, (odds x e : ℝ≥0∞) := by
  refine ⟨exists_good_assignment Value μ scope bad hbad rule x hx_lt_one hprob, ?_⟩
  refine ⟨?_, expectedTotalResamplings_le Value μ scope bad hbad rule x
    hx_lt_one hprob⟩
  intro root
  exact expectedResamplings_le Value μ scope bad hbad rule x hx_lt_one hprob root

end Resampling

end Lax41Proofs
