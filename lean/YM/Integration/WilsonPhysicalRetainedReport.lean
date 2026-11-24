import YM.Integration.WilsonVariableReportWeights

/-! Return the complete original tested moving product, in all signed
grades, to its genuine retained cutoff labels on every reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalRetainedReport
open Function Filter Real MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Source Labels Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open MultilinearCellCapture FilteredIntrinsicGramReadout FilteredWilsonProduct SharedIntrinsicWilsonGrid
open PhysicalNext.Repeat.Legato WilsonPhysicalReportWeights
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {S : Table R.family.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

theorem all_inputs (hG : G.Simple) (F : Spec.Final R.family f S) (fac : Facilities R.family f S)
    (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Z : (g : Grades d) → ℝ → (I → Cover) → Indices R.family (levels g) → (ℕ×ℕ) → R.family.label D,
    ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → PhysMS.tower S),
    PhysMS.Leading F J → ∀ A : ℝ,
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot R.family (P.b t) (P.middle t) (P.j t) x →
      ∀ᶠ w in f.fuse, ∀ v : (k : I) → (Climb.Bel R.family.book).Field (d k), ∃ (ho : Opened R.family D (P.b t) w.2) (live : P.b t≤w.1),
        let Y := field F Q J v t (P.j t) x w
        let total := ∑ g : Grades d, ∑ a, weight (component F Q J v g t) a • Z g t x a w
        Booked R.family w.1 w.2 D Y (P.b t) live ∧ ∀ i≥P.b t, i≤P.j t → i≤w.1 →
          mCost R.family D w.1 w.2 i (topReport R.family w.1 w.2 D R.makes (P.b t) ho live Y -
            (R.family.factory D w.1 w.2).terminal.symm total) ≤ exp (-A*LogV t)*(∏ k,‖v k‖) := by
  classical
  choose Z bank using fun g : Grades d => WilsonFundedProductReportWeights.original
    (d:=levels g) R hG F fac anchor (subgrid P g)
  obtain ⟨U,openU⟩ := eventually_atTop.1 (open_late R.family hG D)
  refine ⟨Z,?_⟩
  intro Q J H A
  filter_upwards [Filter.eventually_all.2 (fun g => bank g (A+2)),WilsonVariableReportWeights.paid (d:=d) F Q J H,
    P.coarse.grows.eventually_ge_atTop U] with t booked fees late
  intro x plot
  filter_upwards [Filter.eventually_all.2 (fun g => booked g x plot)] with w buys
  intro v
  let vg := fun g : Grades d => component F Q J v g t
  let fields := fun g : Grades d => leaves R.family (P.j t) (levels g) x (vg g) w.1 w.2
  let z := fun g : Grades d => ∑ a, weight (vg g) a • Z g t x a w
  obtain ⟨ho,live,_,_⟩ := buys (fun _ => 0) (vg _)
  let Fout := topReport R.family w.1 w.2 D R.makes (P.b t) ho live
  let reporter := (R.family.factory D w.1 w.2).terminal
  let gap := fun g : Grades d => Fout (fields g) - reporter.symm (z g)
  have rows (g : Grades d) : Booked R.family w.1 w.2 D (fields g) (P.b t) live ∧ ∀ i≥P.b t,
      i≤P.j t → i≤w.1 → mCost R.family D w.1 w.2 i (gap g) ≤ gradePrice F Q J v g t*exp (-(A+2)*LogV t) := by
    obtain ⟨_,_,bk,order⟩ := buys g (vg g)
    exact ⟨bk,order⟩
  have cont (g : Grades d) : Continuous (fields g) := by
    change Continuous (∏ i, R.family.O w.1 w.2 (vg g i) (Cells.location R.family.S (P.j t) w.1 w.2 (x i)))
    rw [show (∏ i, R.family.O w.1 w.2 (vg g i) (Cells.location R.family.S (P.j t) w.1 w.2 (x i))) =
      fun V => ∏ i, R.family.O w.1 w.2 (vg g i) (Cells.location R.family.S (P.j t) w.1 w.2 (x i)) V
      from funext fun V => Finset.prod_apply ..]
    exact continuous_finsetProd _ fun i _ => R.family.continuousO ..
  have sumrows := IntrinsicProductLinearity.booked_sum R.family w.1 w.2 D (P.b t) R.makes ho live
    (fun _ : Grades d => (1:ℂ)) fields cont (fun g => (rows g).1)
  simp only [one_smul] at sumrows
  have fsum : field F Q J v t (P.j t) x w = ∑ g, fields g := field_expansion F Q J v t _ x w
  refine ⟨ho,live,?_,?_⟩
  · rw [fsum]; exact sumrows.1
  · intro i bi ij iN
    have actual : Fout (field F Q J v t (P.j t) x w) = ∑ g, Fout (fields g) := (congrArg Fout fsum).trans sumrows.2
    have folded : Fout (field F Q J v t (P.j t) x w) - reporter.symm (∑ g, z g) = ∑ g, gap g := by
      rw [actual,map_sum,←Finset.sum_sub_distrib]
    have cost := IntrinsicProductLinearity.cost_sum R.family w.1 w.2 D i R.makes (openU i (late.trans bi) w.2) iN
      (fun _ : Grades d => (1:ℂ)) gap
    simp only [one_smul,norm_one,one_mul] at cost
    calc
      _ = mCost R.family D w.1 w.2 i (∑ g, gap g) := congrArg (mCost R.family D w.1 w.2 i) folded
      _ ≤ ∑ g, mCost R.family D w.1 w.2 i (gap g) := cost
      _ ≤ ∑ g, gradePrice F Q J v g t*exp (-(A+2)*LogV t) :=
        Finset.sum_le_sum fun g _ => (rows g).2 i bi ij iN
      _ = (∑ g, gradePrice F Q J v g t)*exp (-(A+2)*LogV t) := (Finset.sum_mul ..).symm
      _ ≤ (exp (2*LogV t)*(∏ k,‖v k‖))*exp (-(A+2)*LogV t) := mul_le_mul_of_nonneg_right (fees v) (exp_pos _).le
      _ = (exp (2*LogV t)*exp (-(A+2)*LogV t))*(∏ k,‖v k‖) := by ring
      _ = exp (-A*LogV t)*(∏ k,‖v k‖) := by rw [←exp_add]; exact congrArg (fun c : ℝ => exp c*(∏ k,‖v k‖)) (by ring)

theorem original (hG : G.Simple) (F : Spec.Final R.family f S) (fac : Facilities R.family f S)
    (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Z : (g : Grades d) → ℝ → (I → Cover) → Indices R.family (levels g) → (ℕ×ℕ) → R.family.label D,
    ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → PhysMS.tower S),
    PhysMS.Leading F J → ∀ (v : (k : I) → (Climb.Bel R.family.book).Field (d k)) (A : ℝ),
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot R.family (P.b t) (P.middle t) (P.j t) x →
      ∀ᶠ w in f.fuse, ∃ (ho : Opened R.family D (P.b t) w.2) (live : P.b t≤w.1),
        let Y := field F Q J v t (P.j t) x w
        let total := ∑ g : Grades d, ∑ a, weight (component F Q J v g t) a • Z g t x a w
        Booked R.family w.1 w.2 D Y (P.b t) live ∧ ∀ i≥P.b t, i≤P.j t → i≤w.1 →
          mCost R.family D w.1 w.2 i (topReport R.family w.1 w.2 D R.makes (P.b t) ho live Y -
            (R.family.factory D w.1 w.2).terminal.symm total) ≤ exp (-A*LogV t) := by
  obtain ⟨Z,bank⟩ := all_inputs (d:=d) R hG F fac anchor P
  refine ⟨Z,?_⟩
  intro Q J H v A
  have fixedFee := (Real.tendsto_exp_atTop.comp PhysMS.to_log_zoom).eventually_ge_atTop (∏ k,‖v k‖)
  filter_upwards [bank Q J H (A+1),fixedFee] with t rows fees
  intro x plot
  filter_upwards [rows x plot] with w row
  obtain ⟨ho,live,bought,price⟩ := row v
  refine ⟨ho,live,bought,?_⟩
  intro i bi ij iN
  calc
    _ ≤ exp (-(A+1)*LogV t)*(∏ k,‖v k‖) := price i bi ij iN
    _ ≤ exp (-(A+1)*LogV t)*exp (LogV t) := mul_le_mul_of_nonneg_left fees (exp_pos _).le
    _ = exp (-A*LogV t) := by rw [←exp_add]; exact congrArg exp (by ring)

end YM.Integration.WilsonPhysicalRetainedReport
