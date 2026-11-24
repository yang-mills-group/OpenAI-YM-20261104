import YM.Integration.WilsonFundedProductReportDates

/-! All permitted signed weights return to the same retained finite
product labels; their explicit norm is charged at every reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFundedProductReportWeights
open Function Filter Real MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Source Labels Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open MultilinearCellCapture SharedIntrinsicWilsonGrid PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {S : Table R.family.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

theorem original (hG : G.Simple) (F : Spec.Final R.family f S) (fac : Facilities R.family f S)
    (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Z : ℝ → (I → Cover) → Indices R.family d → (ℕ×ℕ) → R.family.label D,
    ∀ A : ℝ, ∀ᶠ t in trail, ∀ x : I → Cover, Plot R.family (P.b t) (P.middle t) (P.j t) x →
      ∀ᶠ w in f.fuse, ∀ v : (k : I) → R.family.label (d k),
        ∃ (ho : Opened R.family D (P.b t) w.2) (live : P.b t ≤ w.1),
          let Y := leaves R.family (P.j t) d x v w.1 w.2
          let reporter := (R.family.factory D w.1 w.2).terminal
          Booked R.family w.1 w.2 D Y (P.b t) live ∧ ∀ i≥P.b t, i≤P.j t → i≤w.1 →
            mCost R.family D w.1 w.2 i (topReport R.family w.1 w.2 D R.makes (P.b t) ho live Y -
              reporter.symm (∑ a, weight v a • Z t x a w)) ≤ (∑ a, ‖weight v a‖)*exp (-A*LogV t) := by
  classical
  obtain ⟨Z,bank⟩ := WilsonFundedProductReportDates.original (d:=d) R hG F fac anchor P
  obtain ⟨U,openU⟩ := eventually_atTop.1 (open_late R.family hG D)
  refine ⟨Z,?_⟩
  intro A
  filter_upwards [bank A,P.coarse.grows.eventually_ge_atTop U] with t runs late
  intro x plot
  filter_upwards [runs x plot] with w rows
  intro v
  obtain ⟨ho,live,_,_⟩ := rows (fun _ => 0)
  let fields := fun a : Indices R.family d => leaves R.family (P.j t) d x (basisLabels a) w.1 w.2
  let Fout := topReport R.family w.1 w.2 D R.makes (P.b t) ho live
  let reporter := (R.family.factory D w.1 w.2).terminal
  let gap := fun a : Indices R.family d => Fout (fields a)-reporter.symm (Z t x a w)
  have insured (a : Indices R.family d) : Booked R.family w.1 w.2 D (fields a) (P.b t) live ∧
      ∀ i≥P.b t, i≤P.j t → i≤w.1 → mCost R.family D w.1 w.2 i (gap a) ≤ exp (-A*LogV t) := by
    obtain ⟨_,_,ok,matched⟩ := rows a
    exact ⟨ok,matched⟩
  have cont (a : Indices R.family d) : Continuous (fields a) := by
    change Continuous (∏ i, R.family.O w.1 w.2 (basisLabels a i) (Cells.location R.family.S (P.j t) w.1 w.2 (x i)))
    rw [show (∏ i, R.family.O w.1 w.2 (basisLabels a i) (Cells.location R.family.S (P.j t) w.1 w.2 (x i))) =
      fun V => ∏ i, R.family.O w.1 w.2 (basisLabels a i) (Cells.location R.family.S (P.j t) w.1 w.2 (x i)) V from
      funext fun V => Finset.prod_apply ..]
    exact continuous_finsetProd _ fun i _ => R.family.continuousO ..
  have mixed := IntrinsicProductLinearity.booked_sum R.family w.1 w.2 D (P.b t) R.makes ho live
    (weight v) fields cont (fun a => (insured a).1)
  refine ⟨ho,live,?_,?_⟩
  · rw [leaves_expansion (P.j t) w.1 w.2 x v]; exact mixed.1
  · intro i bi ij iN
    have together : Fout (leaves R.family (P.j t) d x v w.1 w.2) - reporter.symm (∑ a, weight v a • Z t x a w) =
        ∑ a, weight v a • gap a := by
      have actual : Fout (leaves R.family (P.j t) d x v w.1 w.2) = ∑ a, weight v a • Fout (fields a) :=
        (congrArg Fout (leaves_expansion (P.j t) w.1 w.2 x v)).trans mixed.2
      rw [actual,map_sum,←Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by dsimp only [gap]; rw [map_smul,smul_sub]
    calc
      _ = mCost R.family D w.1 w.2 i (∑ a, weight v a • gap a) := congrArg (mCost R.family D w.1 w.2 i) together
      _ ≤ ∑ a, ‖weight v a‖*mCost R.family D w.1 w.2 i (gap a) :=
        IntrinsicProductLinearity.cost_sum R.family w.1 w.2 D i R.makes (openU i (late.trans bi) w.2) iN (weight v) gap
      _ ≤ ∑ a, ‖weight v a‖*exp (-A*LogV t) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ((insured a).2 i bi ij iN) (norm_nonneg _)
      _ = _ := (Finset.sum_mul ..).symm

end YM.Integration.WilsonFundedProductReportWeights
