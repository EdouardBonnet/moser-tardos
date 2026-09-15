import Mathlib
import Lax296731.MoserTardosDefinitions

/-!
---
title: Definitions for the Haeupler–Saha–Srinivasan distributional theorem
type: definition
---
Fix a finite collection of mutually independent random variables and a finite
set of bad events determined by them.  The Moser--Tardos algorithm repeatedly
resamples a currently true bad event.  Besides the bad events, we may observe
any other event $B$ determined by the same variables.  This file defines the
bad-event restriction of the event family, the dependency neighborhood
$\Gamma(B)$, the event that $B$ is true at some stage of the algorithm, and
the event that $B$ is true in its final output.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax296731.HaeuplerSahaSrinivasanDefinitions

open Lax296731.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]
variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]
variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- An event belonging to the finite family on which the algorithm runs. -/
abbrev BadEventIndex (badEvents : Finset Event) := {A // A ∈ badEvents}

/-- The variables determining a bad event. -/
def badEventVariables (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable) :
    BadEventIndex badEvents → Finset Variable :=
  fun A ↦ variablesOf A.1

/-- The local set defining a bad event. -/
def badEventSet (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A))) :
    ∀ A, Set (LocalAssignment Value (badEventVariables badEvents variablesOf A)) :=
  fun A ↦ event A.1

/--
The bad events other than `B` that share at least one determining variable
with `B`.
-/
def dependencyNeighborhood (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable) (B : Event) :
    Finset (BadEventIndex badEvents) :=
  Finset.univ.filter fun A ↦
    A.1 ≠ B ∧ ¬Disjoint (variablesOf A.1) (variablesOf B)

/-- The observed event `B` is true in the assignment at stage `n`. -/
def eventOccursAt (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (table : ResamplingTable Value) (B : Event) (n : Nat) : Prop :=
  violates Value variablesOf event
    (currentAssignment Value table
      (runCounts Value (badEventVariables badEvents variablesOf)
        (badEventSet Value badEvents variablesOf event) selectionRule table n)) B

/-- The set of sample tables on which `B` is true at least once. -/
def eventEverOccurs (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : Set (ResamplingTable Value) :=
  {table | ∃ n, eventOccursAt Value badEvents variablesOf event selectionRule table B n}

/--
The first stage at which the algorithm has terminated.  On a nonterminating
table it is set to zero; under the local-lemma hypotheses that exceptional set
has probability zero.
-/
noncomputable def outputTime (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (table : ResamplingTable Value) : Nat := by
  classical
  exact if h : ∃ n, resamplingLog Value (badEventVariables badEvents variablesOf)
        (badEventSet Value badEvents variablesOf event) selectionRule table n = none
      then Nat.find h
      else 0

/-- The assignment returned when the resampling algorithm terminates. -/
noncomputable def outputAssignment (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (table : ResamplingTable Value) : Assignment Value :=
  currentAssignment Value table
    (runCounts Value (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event) selectionRule table
      (outputTime Value badEvents variablesOf event selectionRule table))

/-- The set of sample tables whose output assignment makes `B` true. -/
noncomputable def eventOccursInOutput (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : Set (ResamplingTable Value) :=
  {table | violates Value variablesOf event
    (outputAssignment Value badEvents variablesOf event selectionRule table) B}

/-- The probability that `B` is true at least once during the algorithm. -/
noncomputable def probabilityEventEverOccurs
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (badEvents : Finset Event) (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : ℝ≥0∞ :=
  tableMeasure Value distribution
    (eventEverOccurs Value badEvents variablesOf event selectionRule B)

/-- The probability that `B` is true in the algorithm's output. -/
noncomputable def probabilityEventInOutput
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (badEvents : Finset Event) (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : ℝ≥0∞ :=
  tableMeasure Value distribution
    (eventOccursInOutput Value badEvents variablesOf event selectionRule B)

end Lax296731.HaeuplerSahaSrinivasanDefinitions
