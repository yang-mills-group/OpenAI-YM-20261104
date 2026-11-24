import YM.Integration.WilsonFundedProductReportWeights

/-! The true moving physical reader supplies the whole signed grade
roster. Its total coefficient price is subexponential on the actual
observation clock, so an arbitrary engineering accuracy survives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalReportWeights
open Function Filter Real MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Source Labels Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open MultilinearCellCapture FilteredIntrinsicGramReadout FilteredWilsonProduct SharedIntrinsicWilsonGrid
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

def subgrid (P : Plan C D (Fintype.card I) (∑ i,d i)) (g : Grades d) :
    Plan C D (Fintype.card I) (∑ i,levels g i) :=
  ⟨P.b,P.middle,P.j,P.h,P.a,P.c,P.coarse,P.mid,P.fine,P.pos,P.before,P.low,P.high,by
    have hk : (∑ i,levels g i) ≤ ∑ i,d i :=
      Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (g i).isLt
    have smaller := mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ) |>.mpr hk) (sub_nonneg.mpr P.high.le)
    have good := P.margin
    dsimp [Margin] at good ⊢
    linarith⟩

def gradePrice (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i)) (g : Grades d) (t : ℝ) : ℝ :=
  ∑ a, ‖weight (component F Q J v g t) a‖

theorem price (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∀ᶠ t in trail, (∑ g : Grades d, gradePrice F Q J v g t) ≤ exp (LogV t) := by
  have each (g : Grades d) : RateLE trail LogV (gradePrice F Q J v g) 0 := by
    have fee := weighted_rate PhysMS.to_log_zoom (component F Q J v g)
      (fun _ _ => (1:ℝ)) (fun i => -(levels g i : ℝ)) 0
      (component_rate F Q J H v g) (fun _ => RateLE.const 1 PhysMS.to_log_zoom)
    have cost : RateLE trail LogV (gradePrice F Q J v g) (∑ i, -(levels g i : ℝ)) := by
      change RateLE trail LogV (fun t => ∑ a, ‖weight (component F Q J v g t) a‖) _
      simpa only [mul_one,add_zero] using fee
    exact cost.mono (Finset.sum_nonpos fun i _ => neg_nonpos.mpr (Nat.cast_nonneg _))
  have total : RateLE trail LogV (fun t => ∑ g : Grades d, gradePrice F Q J v g t) 0 :=
    RateLE.sum PhysMS.to_log_zoom (fun g _ => each g)
  filter_upwards [(RateIs.exp 1 PhysMS.to_log_zoom).outweigh total zero_lt_one PhysMS.to_log_zoom] with t cash
  simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun g _ =>
    show 0 ≤ gradePrice F Q J v g t from Finset.sum_nonneg fun _ _ => norm_nonneg _)] using cash

end YM.Integration.WilsonPhysicalReportWeights
