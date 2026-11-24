import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskGram
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskPlaced

/-! Physical mask in the genuine direct four-edge Wilson term of the old
quadratic packet, on the actual support of its own lower row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory OPE.Therm
open AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
open private capped_mask from YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskSeries
variable {G : Gauge} {n : Side}

def maskedFace (K : PathData G) (c : Clip) (p : BudgetPoint) (v : Seat n) (U : Config G n) : ℝ:=
  ∑a : PlaqAxes,(Low.maskedPlain K c (a,Sum.inl ()) (0:Site n) p) (v.view U)

def faceSeat (G : Gauge) (v : Seat n) (U : Config G n) : ℝ:=∑a : PlaqAxes,G.price (faceValue (v.view U) (0,a))

theorem spring_mask_face (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per (K : PathData G) (c : Clip) (v : Seat (R.family.side j per)),
      let p:=(R.family.path.rep N per j).p
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let A:=(Fintype.card PlaqAxes:ℝ)*(|c.direct| *2)
      let f (U : Config G (R.family.side j per)):=maskedFace K c p v U-c.direct*faceSeat G v U
      Measurable f ∧ (∀U,‖f U‖≤A) ∧ (∫U,‖f U‖ ∂scene R.family.path N per j) ≤ A*((2*p.B+1)^4*fee) := by
  filter_upwards [spring_mask_faces R simple heat q] with j paid N live per K c v p fee A f
  let n:=R.family.side j per
  let X:=halo p.B ({0}:Support n)
  let g (a : PlaqAxes) (U : Config G n):=c.direct*G.price (faceValue U (0,a))
  let H (a : PlaqAxes) (U : Config G n):=masked p.threshold X (g a) (v.view U)-g a (v.view U)
  have same : f=fun U=>∑a,H a U:=by
    funext U
    dsimp only [f,maskedFace,faceSeat,H,g]
    rw [mul_sum,←sum_sub_distrib]
    rfl
  have cap (a U) : ‖g a U‖≤|c.direct| *2:=by
    change ‖c.direct*G.price (faceValue U (0,a))‖≤_
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (G.price_range _).1]
    exact mul_le_mul_of_nonneg_left (G.price_range _).2 (abs_nonneg _)
  have size : (X.card:ℝ)≤(2*(p.B:ℝ)+1)^4:=by
    exact_mod_cast (show X.card≤(2*p.B+1)^4 by
      simpa only [card_singleton,one_mul,two_mul] using Corona.halo_size ({0}:Support n) p.B)
  have fe : 0≤fee:=mul_nonneg (by positivity) (pow_nonneg (Real.exp_pos _).le _)
  let μ:=scene R.family.path N per j
  letI : IsProbabilityMeasure μ:=probability R.makes.wilson live
  have part (a : PlaqAxes) : Measurable (H a) ∧ (∀U,‖H a U‖≤|c.direct| *2) ∧
      (∫U,‖H a U‖ ∂μ)≤(|c.direct| *2)*((2*(p.B:ℝ)+1)^4*fee) := by
    have cg : Continuous (g a):=by dsimp only [g,faceValue];fun_prop
    have mg:=cg.measurable
    have A1:Measurable fun U=>masked p.threshold X (g a) (v.view U):=
      (masked_measurable _ _ _ mg).comp (continuous_pull ..).measurable
    have A2:Measurable fun U=>g a (v.view U):=mg.comp (continuous_pull ..).measurable
    refine ⟨A1.sub A2,fun U=>(capped_mask X p.threshold (cap a) (v.view U)).2,?_⟩
    apply (paid N live per X v.1 v.2 (g a) (|c.direct| *2) mg (cap a)).trans
    gcongr
  rw [same]
  have cost:=finite_mask_sum μ H part
  refine ⟨cost.1,cost.2.1,cost.2.2.trans_eq ?_⟩
  dsimp only [A]
  ring

end YM.Integration.OriginalMarkedRunAction
