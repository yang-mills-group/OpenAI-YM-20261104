import YM.Integration.WilsonThermometerPositionFilmCloudReading

/-! Integration through the next honest conditional and its common scalar vacuum divisor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmCloudCommission
open Finset Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Cumulants Comparison.RG02.Order
open YM.Next.SectorChange YM.Primitives.GCC.Anchor WilsonThermometerPositionFilmChartContact
open WilsonThermometerPositionFilmCloudReading
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
  {V':Type} [DecidableEq V'] [Fintype V'] {R':Census V'}
  {S:StepData c f} {clip:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S clip P O) (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors R G f)
  (s:R.Mode) (x:fieldDir G c 1)
local notation "μ" => Gaussian.cloud (K.covariance F tag)
local notation "slice" z:max => Prod.snd (Bulk.translated K F x z)

/-- For this step retain the authentic quiet action while inserting these exact canonical marked rows. -/
def mounted (D:Bulk.Colors R' G f) : Bulk.Colors R' G f := {D with vac:=C.vac}

private theorem blank (w:Bulk.SliceDir S F G) :
    bent S F C R.quiet 0 w=1 ∧ bent S F C R.quiet 1 w=0 := by
  let a:=curve C.power (Bulk.markFn S F C) (1,w)
  let z:=series R 1 a
  have sym:Symmetric z:=⟨a,rfl⟩
  have invisible:z.part (Board R 1).quiet=0:=mark_books C.power (Bulk.markFn S F C) (1,w) 1
  have term:=mark_exp (r:=1) (mark_curve_quiet C.power (Bulk.markFn S F C) (1,w))
  have hz (b:Fin 2):(Order.observe R 1 z b.val).part R.quiet=0:=by
    rw [observation R 1 a (by omega : b.val≤1)]
    exact mark_curve_quiet .. 
  constructor
  · change (PowerSeries.coeff 0 (markExp a)).part R.quiet=_
    rw [←observation R 1 (markExp a) (by decide : 0≤1),term]
    change (First.buc (Poly.pass z)).part R.quiet=_
    exact (congrArg (fun v:Poly R=>v.part R.quiet) (First.buc_pass sym invisible)).trans
      (Poly.pass_part _ (hz 0))
  · change (PowerSeries.coeff 1 (markExp a)).part R.quiet=_
    rw [←observation R 1 (markExp a) (by decide : 1≤1),term]
    change (First.ind (Poly.pass z)).part R.quiet=_
    rw [First.ind_pass (by decide) sym invisible,Poly.quiet_mul,show (First.ind z).part R.quiet=0 from hz 1,zero_mul]

theorem quiet (p:ℕ) (hp:0<p) :
    (First.ind (Bulk.Fk K F tag C x p)).part R.quiet=∫ z,-noise K F tag C x z ∂μ := by
  rw [First.ind,observed K F tag C R.quiet x p 1 hp]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [first, (blank F C (slice z)).1,(blank F C (slice z)).2, mul_one,zero_sub]

theorem integrable_noise : Integrable (noise K F tag C x) μ := by
  apply (integrable K F tag C R.quiet x 1).neg.congr
  filter_upwards [] with z
  change -paid K F tag C R.quiet x 1 z=_
  rw [first,(blank F C (slice z)).1,(blank F C (slice z)).2,mul_one,zero_sub,neg_neg]

theorem normalized (p:ℕ) (hp:0<p) :
    (First.buc (ratio (Bulk.Fk K F tag C x p))).part s=(First.buc (Bulk.Fk K F tag C x p)).part s ∧
    (First.ind (ratio (Bulk.Fk K F tag C x p))).part s=(First.ind (Bulk.Fk K F tag C x p)).part s -
      (First.ind (Bulk.Fk K F tag C x p)).part R.quiet*(First.buc (Bulk.Fk K F tag C x p)).part s := by
  have sym:=Bulk.fk_sym K F tag C x p
  have unit:=Bulk.fk_unit K F tag C x p
  refine ⟨congrArg (fun v:Poly R=>v.part s) (First.buc_ratio sym unit),?_⟩
  have mass:First.ind (denominator (Bulk.Fk K F tag C x p))=
      algebraMap ℂ (Poly R) ((First.ind (Bulk.Fk K F tag C x p)).part R.quiet):=by
    rw [First.ind,denominator,observe_bottom]
    rfl
  rw [First.ind_ratio hp sym unit,mass,←Algebra.smul_def]
  rfl

variable {Q:Type} [Fintype Q] (D:Q→Bulk.Colors R' G f) (a:R'.Mode) (v:Q→ℂ)
variable (H:∀(w:Bulk.SliceDir S F G)(b:Fin 2),bent S F C s b.val w=
  ∑q:Q,v q * bent S F (D q) a b.val w)

include H in
private theorem unnormalized (z:Precision.Key F G→ℝ) (b:Fin 2) :
    paid K F tag C s x b.val z=∑q:Q,v q*paid K F tag (mounted C (D q)) a x b.val z := by
  have free q j:bent S F (mounted C (D q)) a j (slice z)=bent S F (D q) a j (slice z):=rfl
  have left₀:bent S F C s 0 (slice z)=∑q:Q,v q * bent S F (D q) a 0 (slice z):=H (slice z) 0
  have left₁:bent S F C s 1 (slice z)=∑q:Q,v q * bent S F (D q) a 1 (slice z):=H (slice z) 1
  fin_cases b
  · simp only [ground,free]
    exact left₀
  · simp only [first, show ∀q,noise K F tag (mounted C (D q)) x z=noise K F tag C x z from fun _=>rfl,free]
    rw [left₁,left₀]
    simp only [mul_sub,sum_sub_distrib,mul_sum]
    congr 1
    apply sum_congr rfl
    intro q _
    ring

include H in
theorem observed_rows (p:ℕ) (hp:0<p) (b:Fin 2) :
    (Order.observe R p (Bulk.Fk K F tag C x p) b.val).part s=
      ∑q:Q,v q*(Order.observe R' p (Bulk.Fk K F tag (mounted C (D q)) x p) b.val).part a := by
  have fits:b.val≤p:=by omega
  simp_rw [observed _ _ _ _ _ _ _ _ fits]
  calc
    _ = ∫ z,∑q:Q,v q*paid K F tag (mounted C (D q)) a x b.val z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact unnormalized K F tag C s x D a v H z b
    _ = _ := by
      rw [integral_finsetSum univ (fun q _=>(integrable K F tag (mounted C (D q)) a x b.val).const_mul (v q))]
      simp only [integral_const_mul]

include H in
theorem original (p:ℕ) (hp:0<p) (b:Fin 2) :
    (Order.observe R p (ratio (Bulk.Fk K F tag C x p)) b.val).part s=
      ∑q:Q,v q*(Order.observe R' p (ratio (Bulk.Fk K F tag (mounted C (D q)) x p)) b.val).part a := by
  have A:=normalized K F tag C s x p hp
  have B:=fun q=>normalized K F tag (mounted C (D q)) a x p hp
  have scalar q:(First.ind (Bulk.Fk K F tag (mounted C (D q)) x p)).part R'.quiet=
      (First.ind (Bulk.Fk K F tag C x p)).part R.quiet:=
    (quiet K F tag (mounted C (D q)) x p hp).trans (quiet K F tag C x p hp).symm
  have report:=observed_rows K F tag C s x D a v H p hp
  have l₀:(First.buc (Bulk.Fk K F tag C x p)).part s=∑q:Q,v q*(First.buc (Bulk.Fk K F tag (mounted C (D q)) x p)).part a:=report 0
  have l₁:(First.ind (Bulk.Fk K F tag C x p)).part s=∑q:Q,v q*(First.ind (Bulk.Fk K F tag (mounted C (D q)) x p)).part a:=report 1
  fin_cases b
  · change (First.buc _).part s=∑q:Q,v q*(First.buc _).part a
    rw [A.1]
    simp_rw [(B _).1]
    exact report 0
  · change (First.ind _).part s=∑q:Q,v q*(First.ind _).part a
    rw [A.2]
    simp_rw [(B _).2,scalar]
    rw [l₁,l₀]
    simp only [mul_sub,sum_sub_distrib,mul_sum]
    congr 1
    apply sum_congr rfl
    intro q _
    ring

end YM.Integration.WilsonThermometerPositionFilmCloudCommission
