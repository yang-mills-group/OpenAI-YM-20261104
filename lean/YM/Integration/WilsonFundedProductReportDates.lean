import YM.Integration.WilsonRetainedReturnPrice
import YM.Integration.SharedIntrinsicWilsonGrid
import YM.Integration.FundedIntrinsicProduct

/-! The actual retained product and its measured periodic projection
agree to every prescribed engineering order through every reporting
date of the same physical grid, before all regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFundedProductReportDates
open Function Filter Real MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Source Labels Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open MultilinearCellCapture FundedIntrinsicProduct SharedIntrinsicWilsonGrid PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {S : Table R.family.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

theorem original (hG : G.Simple) (F : Spec.Final R.family f S) (fac : Facilities R.family f S)
    (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Z : ℝ → (I → Cover) → Indices R.family d → (ℕ×ℕ) → R.family.label D,
    ∀ A : ℝ, ∀ᶠ t in trail, ∀ x : I → Cover, Plot R.family (P.b t) (P.middle t) (P.j t) x →
      ∀ᶠ w in f.fuse, ∀ a : Indices R.family d,
        ∃ (ho : Opened R.family D (P.b t) w.2) (live : P.b t ≤ w.1),
          let Y := leaves R.family (P.j t) d x (basisLabels a) w.1 w.2
          Booked R.family w.1 w.2 D Y (P.b t) live ∧
          ∀ i≥P.b t, i≤P.j t → i≤w.1 →
            mCost R.family D w.1 w.2 i (topReport R.family w.1 w.2 D R.makes (P.b t) ho live Y -
              (R.family.factory D w.1 w.2).terminal.symm (Z t x a w)) ≤ exp (-A*LogV t) := by
  classical
  obtain ⟨_,_,_,_,gain,fee,Z,_,fund⟩ :=
    FundedIntrinsicProduct.basis (d:=d) F fac anchor PhysMS.to_log_zoom D
      P.coarse P.mid P.fine P.pos P.before (P.low.trans P.high)
  obtain ⟨U,_,back⟩ := WilsonCapturedFactoryReturn.coordinates R hG D
  obtain ⟨M,hM,bound⟩ := back 1 one_pos
  refine ⟨Z,?_⟩
  intro A
  let K := -A-(P.c+1)-1
  have clock := P.fine.pace.eventually_lt_const (show P.c<P.c+1 by linarith)
  have cpos := (R.family.S.divergent.comp P.coarse.grows).eventually_ge_atTop (0:ℝ)
  have cashier := (Real.tendsto_exp_atTop.comp PhysMS.to_log_zoom).eventually_ge_atTop M
  filter_upwards [fund K,P.coarse.grows.eventually_ge_atTop U,clock,cpos,cashier,
    PhysMS.to_log_zoom.eventually_gt_atTop (0:ℝ)] with t supply late tall warm cash tick
  intro x plot
  filter_upwards [Filter.eventually_all.2 (supply x plot)] with w full
  intro a
  obtain ⟨ho,bm,mN,_,keep,capital,_,_,_⟩ := full a
  let hi := bm.trans mN.le
  let Y := leaves R.family (P.j t) d x (basisLabels a) w.1 w.2
  let y := topReport R.family w.1 w.2 D R.makes (P.b t) ho hi Y -
    (R.family.factory D w.1 w.2).terminal.symm (Z t x a w)
  obtain ⟨_,_,_,_,atDate,_⟩ := keep
  refine ⟨ho,hi,(atDate (P.b t) le_rfl bm).2.2.1,?_⟩
  intro i bi ij iN
  have span : 1*(R.family.S.scale i-R.family.S.scale (P.b t)) ≤ (P.c+1)*LogV t := by
    have top := ((div_lt_iff₀ tick).1 tall).le
    have inside := (OPE.scale_mono R.family.S).monotone ij
    calc
      _ = R.family.S.scale i-R.family.S.scale (P.b t) := one_mul _
      _ ≤ R.family.S.scale i := sub_le_self _ warm
      _ ≤ R.family.S.scale (P.j t) := inside
      _ ≤ _ := top
  have charge : mCost R.family D w.1 w.2 (P.b t) y ≤ exp (K*LogV t) := capital
  calc
    _ ≤ M*(exp (1*(R.family.S.scale i-R.family.S.scale (P.b t)))*exp (K*LogV t)) :=
      (bound (P.b t) late w.1 w.2 i bi iN y).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left charge (exp_pos _).le) (by linarith))
    _ ≤ exp (LogV t)*(exp ((P.c+1)*LogV t)*exp (K*LogV t)) :=
      mul_le_mul cash (mul_le_mul_of_nonneg_right (exp_le_exp.mpr span) (exp_pos _).le)
        (by positivity) (exp_pos _).le
    _ = exp (-A*LogV t) := by
      rw [←exp_add,←exp_add]
      exact congrArg exp (by dsimp [K]; ring)

end YM.Integration.WilsonFundedProductReportDates
