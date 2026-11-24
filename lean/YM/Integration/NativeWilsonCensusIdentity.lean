import YM.Integration.NativeRegulatorWilsonFloor
import YM.Integration.OriginalWilsonCensusStep
import YM.Comparison.RG02.Adjacent.Actual

/-! The retained first-block Census action and the explicit local Gaussian
remainder on that same nonlinear Wilson density at positive coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeWilsonCensusIdentity

open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Marker Multi Exterior
open PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Integral Comparison.RG02.Actual
open Comparison.RG02.Order Comparison.RG02.Symmetry Comparison.RG02.Symmetry.Orbit
open Push.SectorMeasure Next.SectorChange Tree
open scoped Classical Topology BigOperators

variable {G : Gauge} (R : Run G) {V : Type} [Fintype V] [DecidableEq V]
  (S : Census V) (i : V) (m p : ℕ) {n : ℕ} (B : Boot.Scout (G := G) n)
  (F : Forest (R.family.path.levels.clock.op m p).ratio)
  (tag : (R.family.path.levels.clock.op m p).Choices) (r : ℕ)

local notation "ρ" => R.family.path.rep (m+1) p (m+1)
local notation "ρ₁" => R.family.path.rep (m+1) p m
local notation "τ" => Pert.Asymptotics.regulatorRun R.family (m+1) p (m+1)
local notation "K" => (RunFormalChain.fromRun R).step (m+1) m p (Nat.lt_succ_self m)
local notation "Δ" => R.family.path.levels.clock.op m p
local notation "Π" => NativeRegulatorWilsonFloor.source R S i (m+1) p B
local notation "W" => Boot.ink S i R.family.path (m+1) p B
local notation "E₁" => fieldDir G (R.family.side m p) 1

def remainder (x : E₁) : ℝ :=
  Local.vacuumError ρ Π K τ F tag W (fun _ => Integral.zone K (ρ).p F τ x) x r

def formal (x : E₁) : ℂ := Adjacent.cover (Symmetry.Orbit.ground K F tag W r) r τ x

local notation:max "e" x:max => remainder R S i m p B F tag r x
local notation:max "u" x:max => formal R S i m p B F tag r x

theorem density (x : E₁) : (ρ₁).eval (Integral.sample τ x) =
    Integral.office K F tag τ (Actual.levelScalar ρ) 0 * Real.exp ((u x).re + e x) := by
  exact (NativeRegulatorWilsonFloor.first R S i p B m F tag x r).1.trans
    (Adjacent.RealStep.hatch K F tag W x τ r (Actual.levelScalar ρ) (e x))

/-- Centering the same finite physical density removes the full vacuum
normalizing scalar and exhibits exactly the change in native remainder. -/
theorem centered (x : E₁) :
    Real.log ((ρ₁).eval 1 / (ρ₁).eval (Integral.sample τ x)) + (u x-u 0).re = e 0-e x := by
  have h₀ := density R S i m p B F tag r (0 : E₁)
  rw [show Integral.sample τ (0 : E₁) = 1 from by simp [Integral.sample]] at h₀
  have hp : 0 < Integral.office K F tag τ (Actual.levelScalar ρ) (0:E₁) :=
    Integral.office_pos K F tag τ (Actual.levelScalar ρ) 0
      (Local.RealStep.coupling_pos R.family (m+1) p (m+1) R.makes le_rfl)
  have hy z : 0 < (ρ₁).eval z := RG02.Actual.eval_pos R.makes.wilson (Nat.le_succ m) z
  rw [Real.log_div (hy 1).ne' (hy _).ne',h₀,density R S i m p B F tag r x,
    Real.log_mul hp.ne' (Real.exp_pos _).ne',Real.log_mul hp.ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_exp,Complex.sub_re]
  ring

open FullQLocal.RenderedStep
variable {I : Type} {J : FullQLocal.RenderedStep.Request I}
  (A : NumericSchedule R.family J) {ε : ℝ}

theorem kept (H : OriginalWilsonCensusStep.Receipt R A ε m p) (x : E₁)
    (hx : flags (ρ₁).p.threshold (Integral.sample τ x) = ∅) :
    let Z := OriginalCensusBarcode.carrier R A m (m+1) p (Nat.lt_succ_self m)
    let a := OriginalWilsonCensusStep.keptAction R m p J.order
    let z := Integral.sample τ x
    a z - a 1 + (ρ₁).path.inChannels (ρ₁).clip (ρ₁).p (ρ₁).beta z +
      Z.activities.additive (A.outputNorm m) z +
      (formal R S i m p B F tag J.order x - formal R S i m p B F tag J.order 0).re =
      remainder R S i m p B F tag J.order 0 - remainder R S i m p B F tag J.order x := by
  intro Z a z
  obtain ⟨_,_,_,_,h⟩ := H
  have hc := h z hx
  rw [← OriginalWilsonCensusStep.recorded R m p] at hc
  have hs := centered R S i m p B F tag J.order x
  linarith only [hc,hs]

end YM.Integration.NativeWilsonCensusIdentity
end
