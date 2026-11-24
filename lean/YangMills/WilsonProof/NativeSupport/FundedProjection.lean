import YangMills.WilsonProof.NativeSupport.ScalarCompensation
import YM.FullVolume.Fares.Dusk
import YM.FullVolume.Nectar.Emits

/-! The physical funded run pays for arbitrarily many dated roots at a coarse
site by a single inverse multiplicity. Its support exponent also pays for a
fixed stencil in units of an actual block factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Lattice RG Wilson Filter PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Campaign PhysicalNext.Repeat.Muse.Veil
open PhysicalNext.Repeat.Legato.Campaign.Face
open PhysicalNext.JointLoad.Heir Push.PriceCompiler
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {T : Campaign R}
variable {Θ : Luna.Tableau T.width 300} {v : ℕ → ℕ → ℝ} (sky : Sky R T Θ v)
include sky

theorem occupied_rooms (j N per : ℕ) (hj : j < N) (M : ℕ) (hm : 0 < M) :
    ∃ a : ℝ, creditP (timeEntry R (j+1))/(M:ℝ) ≤ a ∧
      Rooms (T.L.prim N j per hj) Θ M a T.pay T.pay := by
  obtain ⟨b,h⟩ := sky.receives j N per hj
  refine ⟨b/M, div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _), ?_⟩
  · exact (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le h.positive.le)).trans h.foldE
  · exact { h.rooms with bill := palette_multiplicity h.rooms.bill M hm }

theorem fixed_stencil_fee (j s : ℕ) :
    Real.exp (((R.alloy.B.a.budget j).supportExponent+2) * s) ≤
      ((R.alloy.B.a.S.block j).val : ℝ)^s := by
  let L := R.alloy.B.a
  have f := sky.fee _ _ (step_paid L j)
  rw [← params_eq R.alloy.B.valid j, ← block_eq R.alloy.B.valid j] at f
  let r := R.kit.span (L.clock.J (j+1)) (L.clock.J j)
  let a := (L.budget j).supportExponent+2
  change Real.exp (a * (Planned.AtomRegular.toll r : ℝ)) ≤ (L.S.block j).val at f
  have ha : 0 ≤ a := by
    have hs := sky.supports j
    change 100 ≤ (L.budget j).supportExponent at hs
    dsimp only [a]
    linarith
  have ht : 1 ≤ (Planned.AtomRegular.toll r : ℝ) := by
    have hz : 0 < Planned.AtomRegular.toll r := by unfold Planned.AtomRegular.toll; positivity
    exact_mod_cast (Nat.succ_le_of_lt hz)
  have fee : Real.exp a ≤ (L.S.block j).val :=
    (Real.exp_le_exp.mpr (le_mul_of_one_le_right ha ht)).trans f
  change Real.exp (a*(s:ℝ)) ≤ ((L.S.block j).val : ℝ)^s
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos a).le fee s

end YM.Integration.InletSusceptibility
