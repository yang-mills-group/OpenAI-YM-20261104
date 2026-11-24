import YM.Integration.WilsonFiniteProgramWholeSource
import YM.FVAAlt2.Boot.Labels

/-! The actual multi-source bare Wilson program and the whole ordinary position source
agree at every finite coefficient on the original first block. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramWholeBirth
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PhysicalNext.Repeat.Legato PertExtension.Orb.SlotEvaluation
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick RegulatorIR.FVAAlt2.Booth
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} (C : Run G) (i per : ℕ)
    {I J : Type} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]
    (R : Census I) (R' : Census J) (s : R.Mode) (j : J)
    (d : I → ℕ) (v : (a : I) → (C.family.labels.level (d a)).Index) (z : I → Cover)
local notation "Γ" => RunFormalChain.fromRun C
local notation "Φ" => C.family.path
local notation "c" => C.family.side i per
local notation "f" => C.family.side (i+1) per
local notation "step₀" => (Φ).levels.clock.op i per
local notation "K" => (Γ).step (i+1) i per (Nat.lt_succ_self i)
local notation "coords" => wrap (f) ∘ z
local notation "W" => YM.FVAAlt2.Block.wardrobe C i per R coords d v
local notation "B" => RegulatorIR.FVAAlt2.Boot.scout C s.val d v z
local notation "W'" => RegulatorIR.FVAAlt2.Boot.ink R' j Φ (i+1) per (B)

private lemma scalar (g c₀ : ℝ) (U : Config G f) :
    (Integral.model g c₀ W K U).part R.quiet =
      (Integral.model g c₀ W' K U).part R'.quiet := by
  simp only [Integral.model, Poly.part_smul, Integral.markedLog,
    Poly.pass_part _ (Multi.part_lit_quiet _)]
  rfl

/-- Simultaneous (g^{-d_a}) factors are the compensation for the native total field degree. -/
theorem submitted (g c₀ : ℝ) (U : Config G f) :
    (Integral.model g c₀ W K U).part s =
      (Integral.model g c₀ W' K U).part (R'.fire j) := by
  simp only [Integral.model, Poly.part_smul]
  congr 1
  change (Poly.pass (Integral.markedLog g U
    (YM.FVAAlt2.Block.ink C i per R coords d v))).part s =
    (Poly.pass (Integral.markedLog g U W')).part (R'.fire j)
  rw [YM.FVAAlt2.Block.ink, Bare.Signals.singleton, Cumulants.pass_lambda,
    Multi.first_pass j (Integral.markedLog g U W') (Multi.part_lit_quiet _)]
  rw [show (Integral.markedLog g U W').part (R'.fire j) =
    (g^(W').power (Arm.pub j))⁻¹ • (W').mark (Arm.pub j) g U from
    Multi.part_lit _ (Arm.pub j)]
  simp only [RegulatorIR.FVAAlt2.Boot.ink, eq_self, ↓reduceIte,
    RegulatorIR.FVAAlt2.Boot.scout, topMark, Finset.prod_apply]
  change (∏ a∈s.val, (g ^ (YM.FVAAlt2.Block.depths C d v a))⁻¹ •
    (YM.FVAAlt2.Block.element C i per coords d v a U : ℂ)) =
    (g ^ (∑ a∈s.val, YM.FVAAlt2.Block.depths C d v a))⁻¹ •
      ((∏ a∈s.val, YM.FVAAlt2.Block.element C i per coords d v a U : ℝ) : ℂ)
  simp only [← Finset.prod_pow_eq_pow_sum, Complex.real_smul, Complex.ofReal_prod,
    Complex.ofReal_inv, Complex.ofReal_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem original (F : Forest (step₀).ratio) (t : (step₀).Choices) (A : fieldDir G c 1) (n : ℕ) :
    ∀ k≤n, LocalFormal.runCoefficients C (YM.FVAAlt2.Block.ticket C i per R coords d v F t A) n k s =
      Laplace.detail (Order.ratio (Bulk.Fk K F t W' A n)) (R'.fire j) k := by
  exact WilsonFiniteProgramWholeSource.normalized K F t R R' s W W' (R'.fire j) A 0
    ((Φ).levels.budget i) n (YM.FVAAlt2.Block.dressedTop C i per R coords d v).1.1
    (RegulatorIR.FVAAlt2.Boot.authentic R' j Φ Γ (i+1) per (B)).1
    (fun g => scalar C i per R R' s j d v z g 0)
    (fun g => submitted C i per R R' s j d v z g 0)

end YM.Integration.WilsonPositionProgramWholeBirth
