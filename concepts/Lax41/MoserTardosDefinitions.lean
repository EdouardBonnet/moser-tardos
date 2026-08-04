import Mathlib

/-!
---
title: Definitions for the Moser–Tardos resampling algorithm
type: definition
---
This file gives the semantic closure of the Moser--Tardos theorem.  A bad event
is represented by the set of local assignments on the finite collection of
independent random variables that determines it.  An infinite table supplies
fresh independent samples.  A measurable rule repeatedly chooses a currently
true bad event, whose variables are then advanced to their next samples.  The
definitions below give the dependency neighborhood, the probability of an
event, and the expected number of times each event is resampled.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax41.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]
variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]
variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- A coordinate of the infinite resampling table. -/
abbrev TableIndex := (i : Variable) × Nat

/-- An infinite table of fresh samples, one row for each independent variable. -/
abbrev ResamplingTable := (j : TableIndex (Variable := Variable)) → Value j.1

/-- An assignment to the variables in a finite scope. -/
abbrev LocalAssignment (indices : Finset Variable) :=
  (i : indices) → Value i.1

/-- The product law of an infinite resampling table. -/
noncomputable def tableMeasure
    (distribution : ∀ i, MeasureTheory.Measure (Value i)) :
    MeasureTheory.Measure (ResamplingTable Value) :=
  MeasureTheory.Measure.infinitePi
    fun j : TableIndex (Variable := Variable) ↦ distribution j.1

/-- The product law restricted to a finite collection of variables. -/
noncomputable def localMeasure
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (indices : Finset Variable) :
    MeasureTheory.Measure (LocalAssignment Value indices) :=
  MeasureTheory.Measure.infinitePi fun i : indices ↦ distribution i.1

/-- The probability of a bad event under the original product distribution. -/
noncomputable def eventProbability
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (A : Event) : ℝ≥0∞ :=
  localMeasure Value distribution (variablesOf A) (badEvent A)

/-- A complete assignment to the finite family of independent variables. -/
abbrev Assignment := ∀ i, Value i

/-- Restriction of a complete assignment to an event's scope. -/
def restrictAssignment (variablesOf : Event → Finset Variable)
    (assignment : Assignment Value) (A : Event) :
    LocalAssignment Value (variablesOf A) :=
  fun i ↦ assignment i.1

/-- The bad event `A` is true under `assignment`. -/
def violates (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (assignment : Assignment Value) (A : Event) : Prop :=
  restrictAssignment Value variablesOf assignment A ∈ badEvent A

/--
A measurable deterministic implementation of "choose any currently true bad
event".  It returns `none` exactly when no bad event is true.
-/
structure ResamplingRule (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A))) where
  choose : Assignment Value → Option Event
  measurable_fiber : ∀ result, MeasurableSet {assignment | choose assignment = result}
  sound : ∀ ⦃assignment : Assignment Value⦄ ⦃A : Event⦄,
    choose assignment = some A →
      violates Value variablesOf badEvent assignment A
  complete : ∀ ⦃assignment : Assignment Value⦄,
    choose assignment = none →
      ∀ A, ¬violates Value variablesOf badEvent assignment A

/-- The assignment exposed by a resampling table at the given row counters. -/
def currentAssignment (table : ResamplingTable Value) (counts : Variable → Nat) :
    Assignment Value :=
  fun i ↦ table ⟨i, counts i⟩

/-- Increment precisely the counters in the scope of the selected event. -/
def advanceCounts (variablesOf : Event → Finset Variable)
    (counts : Variable → Nat) (selected : Option Event) : Variable → Nat :=
  selected.elim counts fun A i ↦
    if i ∈ variablesOf A then counts i + 1 else counts i

/-- The row counters after the first `n` iterations of the resampling algorithm. -/
def runCounts (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (table : ResamplingTable Value) : Nat → Variable → Nat :=
  Nat.rec (fun _ ↦ 0) fun _ counts ↦
    advanceCounts variablesOf counts
      (selectionRule.choose (currentAssignment Value table counts))

/-- The event resampled at time `n`, or `none` once no bad event remains. -/
def resamplingLog (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (table : ResamplingTable Value) (n : Nat) : Option Event :=
  selectionRule.choose (currentAssignment Value table
    (runCounts Value variablesOf badEvent selectionRule table n))

/-- The (possibly infinite) number of times the bad event `A` is resampled. -/
noncomputable def resamplingCount (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (table : ResamplingTable Value) (A : Event) : ℝ≥0∞ :=
  ∑' t : Nat, Set.indicator
    {t | resamplingLog Value variablesOf badEvent selectionRule table t = some A}
    (fun _ ↦ (1 : ℝ≥0∞)) t

/-- The expected number of resamplings of one event. -/
noncomputable def expectedResamplings
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (A : Event) : ℝ≥0∞ :=
  ∫⁻ table, resamplingCount Value variablesOf badEvent selectionRule table A
    ∂tableMeasure Value distribution

/-- The other bad events that share at least one random variable with `A`. -/
def dependencyNeighborhood (variablesOf : Event → Finset Variable)
    (A : Event) : Finset Event :=
  Finset.univ.filter fun B ↦
    B ≠ A ∧ ¬Disjoint (variablesOf A) (variablesOf B)

end Lax41.MoserTardosDefinitions
