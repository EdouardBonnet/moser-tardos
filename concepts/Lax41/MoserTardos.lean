import Mathlib

/-!
---
title: The Moser–Tardos theorem
type: theorem
---
Let finitely many mutually independent random variables determine finitely many
measurable bad events.  If numbers $x(A)\in(0,1)$ satisfy
$$
  \Pr[A] \le x(A)\prod_{B\in\Gamma(A)}(1-x(B)),
$$
where $\Gamma(A)$ consists of the other bad events sharing a variable with
$A$, then an assignment avoiding every bad event exists.  Moreover, for any
measurable deterministic rule that selects a currently true bad event, the
sequential resampling algorithm has expected number of resamplings of $A$ at
most $x(A)/(1-x(A))$, and its expected total number of resamplings is at most
the sum of these bounds.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax41.MoserTardos

variable {E : Type} [Fintype E] [DecidableEq E]
variable {I : Type} [instFintypeI : Fintype I] [DecidableEq I]

/-- Two events are related when they are equal or share a random variable. -/
def scopeRelated (scope : E → Finset I) (a b : E) : Prop :=
  a = b ∨ ¬Disjoint (scope a) (scope b)

instance scopeRelated.instDecidable (scope : E → Finset I) :
    DecidableRel (scopeRelated scope) := by
  intro a b
  unfold scopeRelated
  infer_instance

variable (Value : I → Type) [∀ i, MeasurableSpace (Value i)]

/-- A coordinate of the infinite resampling table. -/
abbrev TableIndex := (i : I) × Nat

/-- An infinite table of fresh samples, one row for each independent variable. -/
abbrev ResamplingTable := (j : TableIndex (I := I)) → Value j.1

/-- An assignment to the variables in a finite scope. -/
abbrev LocalAssignment (s : Finset I) := (i : s) → Value i.1

/-- The product law of an infinite resampling table. -/
noncomputable def tableMeasure (μ : ∀ i, MeasureTheory.Measure (Value i)) :
    MeasureTheory.Measure (ResamplingTable Value) :=
  MeasureTheory.Measure.infinitePi fun j : TableIndex (I := I) ↦ μ j.1

/-- The product law restricted to a finite collection of variables. -/
noncomputable def localMeasure (μ : ∀ i, MeasureTheory.Measure (Value i))
    (s : Finset I) : MeasureTheory.Measure (LocalAssignment Value s) :=
  MeasureTheory.Measure.infinitePi fun i : s ↦ μ i.1

/-- The probability of a bad event under the original product distribution. -/
noncomputable def eventProbability
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e))) (e : E) : ℝ≥0∞ :=
  localMeasure Value μ (scope e) (bad e)

/-- A complete assignment to the finite family of independent variables. -/
abbrev Assignment [Fintype I] := ∀ i, Value i

/-- Restriction of a complete assignment to an event's scope. -/
def restrictAssignment (scope : E → Finset I) (a : Assignment Value) (e : E) :
    LocalAssignment Value (scope e) :=
  fun i ↦ a i.1

/-- The bad event `e` is true in assignment `a`. -/
def violates (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (a : Assignment Value) (e : E) : Prop :=
  restrictAssignment Value scope a e ∈ bad e

/-- A measurable deterministic strategy for choosing a currently true bad event. -/
structure SelectionRule (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e))) where
  choose : Assignment Value → Option E
  measurable_fiber : ∀ o, MeasurableSet {a | choose a = o}
  sound : ∀ ⦃a : Assignment Value⦄ ⦃e : E⦄,
    choose a = some e → violates Value scope bad a e
  complete : ∀ ⦃a : Assignment Value⦄,
    choose a = none → ∀ e, ¬violates Value scope bad a e

/-- The assignment exposed by a resampling table at the given row counters. -/
def currentAssignment (table : ResamplingTable Value) (counts : I → Nat) :
    Assignment Value :=
  fun i ↦ table ⟨i, counts i⟩

/-- Increment precisely the counters in the scope of the selected event. -/
def advanceCounts (scope : E → Finset I) (counts : I → Nat)
    (selected : Option E) : I → Nat :=
  selected.elim counts fun e i ↦ if i ∈ scope e then counts i + 1 else counts i

/-- The row counters after the first `n` iterations of the resampling algorithm. -/
def runCounts (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value) :
    Nat → I → Nat :=
  Nat.rec (fun _ ↦ 0) fun _ counts ↦
    advanceCounts scope counts (rule.choose (currentAssignment Value table counts))

/-- The event resampled at time `n`, or `none` once no bad event remains. -/
def resamplingLog (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (n : Nat) : Option E :=
  rule.choose (currentAssignment Value table
    (runCounts Value scope bad rule table n))

/-- The (possibly infinite) number of times event `root` is resampled. -/
noncomputable def resamplingCount (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (table : ResamplingTable Value)
    (root : E) : ℝ≥0∞ :=
  ∑' t : Nat, Set.indicator
    {t | resamplingLog Value scope bad rule table t = some root}
    (fun _ ↦ (1 : ℝ≥0∞)) t

/-- The expected number of resamplings of one event. -/
noncomputable def expectedResamplings
    (μ : ∀ i, MeasureTheory.Measure (Value i)) (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) (root : E) : ℝ≥0∞ :=
  ∫⁻ table, resamplingCount Value scope bad rule table root
    ∂tableMeasure Value μ

/-- The odds $x/(1-x)$. -/
noncomputable def odds (x : E → NNReal) (a : E) : NNReal :=
  x a / (1 - x a)

/-- A factor in the asymmetric local-lemma hypothesis. -/
def localLemmaFactor (scope : E → Finset I) (x : E → NNReal)
    (a b : E) : NNReal :=
  if b ≠ a ∧ ¬Disjoint (scope a) (scope b) then 1 - x b else 1

/-- The right side $x(A)\prod_{B\in\Gamma(A)}(1-x(B))$. -/
noncomputable def localLemmaBound (scope : E → Finset I)
    (x : E → NNReal) (a : E) : NNReal :=
  x a * ∏ b : E, localLemmaFactor scope x a b

/-- The sum of the expected resampling counts of all bad events. -/
noncomputable def expectedTotalResamplings
    (μ : ∀ i, MeasureTheory.Measure (Value i)) (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (rule : SelectionRule Value scope bad) : ℝ≥0∞ :=
  ∑ e : E, expectedResamplings Value μ scope bad rule e

/-- The constructive asymmetric Lovász local lemma of Moser and Tardos. -/
axiom moser_tardos
    (μ : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment Value (scope e)))
    (hbad : ∀ e, MeasurableSet (bad e))
    (rule : SelectionRule Value scope bad) (x : E → NNReal)
    (hx_pos : ∀ a, 0 < x a) (hx_lt_one : ∀ a, x a < 1)
    (hprob : ∀ a, eventProbability Value μ scope bad a ≤
      (localLemmaBound scope x a : ℝ≥0∞)) :
    (∃ a : Assignment Value, ∀ e, ¬violates Value scope bad a e) ∧
      (∀ root, expectedResamplings Value μ scope bad rule root ≤
        (odds x root : ℝ≥0∞)) ∧
      expectedTotalResamplings Value μ scope bad rule ≤
        ∑ e : E, (odds x e : ℝ≥0∞)

end Lax41.MoserTardos
