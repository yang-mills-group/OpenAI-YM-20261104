import YM.Integration.NativeRegulatorInitialDatum
import YM.Comparison.RG02.Step.History

/-! The physical marked Wilson input on the exact finite lattice and its
positive-coupling nonlinear first block, with the full native healthy zone. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorWilsonFloor

open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Marker Multi Exterior
open PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Integral Comparison.RG02.Actual
open Comparison.RG02.Order Push.SectorMeasure Next.SectorChange Tree
open scoped Classical Topology BigOperators

variable {G : Gauge} (R : Run G) {V : Type} [Fintype V] [DecidableEq V]
  (S : Census V) (i : V) (N p : ℕ) {n : ℕ} (B : Boot.Scout (G := G) n)

local notation "f₀" => R.family.side N p
local notation "P₀" => R.family.path.rep N p N
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p N
local notation "W₀" => Boot.ink S i R.family.path N p B

/-- The entire unnormalized finite-volume Gibbs density, including every
original colored coefficient and its physical power of the coupling. -/
def source (U : Config G f₀) : Poly S :=
  (↑(Wilson.bare (R.family.beta N p) U) : ℂ) • (Integral.markedLog g₀ U W₀).pass

private theorem original : (P₀).eval = Wilson.bare (R.family.beta N p) := (R.makes.wilson.starts N p).2

theorem vacuum (U : Config G f₀) : (source R S i N p B U).part S.quiet = ((P₀).eval U : ℂ) := by
  rw [source, Poly.part_smul, Integral.markedLog, Poly.pass_part _ (part_lit_quiet _), mul_one,
    original R N p]

theorem floor : Actual.Floor P₀ (source R S i N p B) := by
  have hw := (Boot.authentic S i R.family.path (RunFormalChain.fromRun R) N p B).1
  refine ⟨vacuum R S i N p B,?_,?_⟩
  · apply Leaf.smul
    · exact Envelope.compactC (Complex.continuous_ofReal.comp (Wilson.bare_cont _))
    · exact Leaf.sum _ _ (fun j => Leaf.smul (Leaf.atom _) (Leaf.pow (Integral.leaf_mark g₀ W₀ hw) j))
  · intro t U
    simp only [source, Wilson.bare_gauge, Integral.markedLog,
      show ∀ b, (W₀).mark b g₀ (gauge t U) = _ from fun b => hw.gauges b g₀ t U]

/-- Before the first physical push, the normalized log of the actual
marked Gibbs density agrees exactly on the entire configuration space. -/
theorem logarithm (U : Config G f₀) :
    Actual.markWeight P₀ (source R S i N p B) U = Integral.markedLog g₀ U W₀ := by
  rw [Actual.markWeight, source, original R N p, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Wilson.bare_pos _ _).ne'), one_smul]
  exact Cumulants.connected_pass (part_lit_quiet _)

theorem zero_error (U : Config G f₀) :
    Actual.errorLog (source R S i N p B) W₀ U g₀ P₀ = 0 := by
  exact sub_eq_zero.mpr (logarithm R S i N p B U)

variable (m : ℕ) (F : Forest (R.family.path.levels.clock.op m p).ratio)
  (tag : (R.family.path.levels.clock.op m p).Choices)
  (x : fieldDir G (R.family.side m p) 1) (r : ℕ)

local notation "ρ" => R.family.path.rep (m+1) p (m+1)
local notation "ρ₁" => R.family.path.rep (m+1) p m
local notation "τ" => Pert.Asymptotics.regulatorRun R.family (m+1) p (m+1)
local notation "K" => (RunFormalChain.fromRun R).step (m+1) m p (Nat.lt_succ_self m)
local notation "Δ" => R.family.path.levels.clock.op m p
local notation "Π" => source R S i (m+1) p B
local notation "W" => Boot.ink S i R.family.path (m+1) p B
local notation "Z" => fun _ : (Δ).Choices => Integral.zone K (ρ).p F τ x
local notation "Q" => Bulk.Fk K F tag W x r
local notation "v₁" => Integral.sample τ x

/-- The first literal Wilson block at positive physical coupling. The native
error is separated from the vacuum, ordinary moments and marked cumulants on
the same nonlinear field. All partitions of the supplied census are kept. -/
theorem first :
    (ρ₁).eval v₁ = Integral.office K F tag τ (Actual.levelScalar ρ) x *
      Real.exp (exponentPrice Q τ + Local.vacuumError ρ Π K τ F tag W Z x r) ∧
    Local.normalized ρ Π Δ v₁ = Order.value (τ : ℂ) (Order.ratio Q) +
      Local.normalizeError ρ Π K τ F tag W Z x r ∧
    Local.cumulant ρ Π Δ v₁ = Order.value (τ : ℂ) (Order.logMarked Q) +
      Local.markingError ρ Π K τ F tag W Z x r (Fintype.card V) ∧
    Actual.Push Δ (ρ).beta Π v₁ = Complex.ofReal ((ρ₁).eval v₁) • (Local.cumulant ρ Π Δ v₁).pass :=
  Local.RealStep.genuine R.family (m+1) p m (RunFormalChain.fromRun R) (Nat.lt_succ_self m)
    Π W F tag x R.makes (floor R S i (m+1) p B)
    (Boot.authentic S i R.family.path (RunFormalChain.fromRun R) (m+1) p B).1 r (Fintype.card V)
    (fun _ => Finset.card_le_univ _) Z (fun _ => (Integral.plausible K F (ρ).p τ x).1)
    (fun _ => Set.Subset.refl _)

end YM.Integration.NativeRegulatorWilsonFloor
end
