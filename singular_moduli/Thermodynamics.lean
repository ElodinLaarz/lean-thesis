import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# First Law of Thermodynamics

This file formalizes the first law of thermodynamics in terms of real-valued
energy, heat, and work quantities.

The **first law** states: for a closed thermodynamic system undergoing a process,
the change in internal energy equals the heat transferred into the system minus
the work done by the system on its surroundings:

  ΔU = Q - W

## Main definitions

* `Thermodynamics.State` — a thermodynamic state carrying an internal energy value
* `Thermodynamics.Process` — a process connecting two states, with associated heat
  and work values
* `Process.deltaU` — the change in internal energy `U_final - U_initial`
* `Process.satisfiesFirstLaw` — the predicate `ΔU = Q - W`

## Main results

* `firstLaw_adiabatic` — adiabatic process (`Q = 0`) implies `ΔU = -W`
* `firstLaw_isochoric` — isochoric process (`W = 0`) implies `ΔU = Q`
* `firstLaw_cyclic` — cyclic process (`ΔU = 0`) implies `Q = W`
* `firstLaw_iff` — equivalent form: `Q = ΔU + W`
* `firstLaw_unique_work` — for fixed states and heat, the work is uniquely
  determined by the first law
-/

namespace Thermodynamics

/-! ### States and processes -/

/-- A thermodynamic state, characterised by its internal energy (in joules). -/
structure State where
  /-- Internal energy of the system (joules). -/
  internalEnergy : ℝ

/-- A thermodynamic process connecting an initial state to a final state.

* `heat` is the heat transferred **into** the system (positive = absorbed).
* `work` is the work done **by** the system on its surroundings (positive = expansion work). -/
structure Process where
  /-- State before the process. -/
  initial : State
  /-- State after the process. -/
  final : State
  /-- Heat transferred into the system. -/
  heat : ℝ
  /-- Work done by the system. -/
  work : ℝ

/-- The change in internal energy `ΔU = U_final - U_initial`. -/
def Process.deltaU (p : Process) : ℝ :=
  p.final.internalEnergy - p.initial.internalEnergy

/-! ### The first law -/

/-- A process **satisfies the first law** if `ΔU = Q - W`. -/
def Process.satisfiesFirstLaw (p : Process) : Prop :=
  p.deltaU = p.heat - p.work

/-! ### Consequences of the first law -/

/-- **Adiabatic processes** (`Q = 0`): the first law reduces to `ΔU = -W`.
All energy change comes from work alone. -/
theorem firstLaw_adiabatic {p : Process} (hadiabatic : p.heat = 0)
    (h : p.satisfiesFirstLaw) : p.deltaU = -p.work := by
  unfold Process.satisfiesFirstLaw at h
  rw [hadiabatic, zero_sub] at h
  exact h

/-- **Isochoric processes** (`W = 0`): the first law reduces to `ΔU = Q`.
All energy change comes from heat alone. -/
theorem firstLaw_isochoric {p : Process} (hisochoric : p.work = 0)
    (h : p.satisfiesFirstLaw) : p.deltaU = p.heat := by
  unfold Process.satisfiesFirstLaw at h
  rw [hisochoric, sub_zero] at h
  exact h

/-- **Cyclic processes** (`ΔU = 0`): the first law reduces to `Q = W`.
Net heat absorbed equals net work done over a full cycle. -/
theorem firstLaw_cyclic {p : Process}
    (hcyclic : p.final.internalEnergy = p.initial.internalEnergy)
    (h : p.satisfiesFirstLaw) : p.heat = p.work := by
  unfold Process.satisfiesFirstLaw Process.deltaU at h
  rw [hcyclic, sub_self] at h
  linarith

/-- Equivalent form of the first law: `Q = ΔU + W`. -/
theorem firstLaw_iff {p : Process} :
    p.satisfiesFirstLaw ↔ p.heat = p.deltaU + p.work := by
  unfold Process.satisfiesFirstLaw
  constructor <;> intro h <;> linarith

/-- **Existence and uniqueness of work**: given fixed initial and final states and a
heat value `Q`, there is a unique work value `W` such that the process satisfies
the first law. -/
theorem firstLaw_unique_work (initial final : State) (Q : ℝ) :
    ∃! W : ℝ, (Process.mk initial final Q W).satisfiesFirstLaw := by
  refine ⟨Q - (final.internalEnergy - initial.internalEnergy), ?_, ?_⟩
  · unfold Process.satisfiesFirstLaw Process.deltaU
    ring
  · intro W hW
    unfold Process.satisfiesFirstLaw Process.deltaU at hW
    linarith

end Thermodynamics
