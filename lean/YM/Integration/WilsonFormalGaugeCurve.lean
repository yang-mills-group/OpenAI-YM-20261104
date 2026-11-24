import YM.Integration.WilsonPublishedPrimerWard

/-! Reading the formal nonlinear Ward on a single real rescaled field
curve with the same coefficients as the physical curvature renderer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFormalGaugeCurve
open Function Filter Finset Lattice Wilson RG FormalBulk08 FormalBulk08.Series
open FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Jets PowerSeries
open PertExtension.Series Tested PositionX.Jet AllOrder AllOrder.Response
open AllOrder.Laplace.SigmaP
open scoped Classical BigOperators Topology ContDiff
variable {I:Type}[Fintype I]

def ray (v:ℝ→Rays I) (x:Rays Unit):Rays I:=x ()•v (x ())
def evaluation (W:Pap I) (i:ℕ) (x:Rays I):ℝ:=traceP x (coeff i W)
def oneRay:Rays Unit:=fun _=>1

theorem ray_smooth (v:ℝ→Rays I)(h:ContDiffAt ℝ ω v 0):
    ContDiffAt ℝ ω (ray v) 0:=by
  have ev:ContDiffAt ℝ ω (fun x:Rays Unit=>x ()) 0:=contDiffAt_apply ..
  exact ev.smul (h.comp 0 ev)

private theorem coordinate (v:ℝ→Rays I)(h:ContDiffAt ℝ ω v 0)(a:I):
    gaze (fun t=>v t a) (glimpse oneRay (motor (ray v) a)):=by
  let f(x:Rays Unit):=ray v x a
  have ok:ContDiffAt ℝ ∞ f 0:=((contDiffAt_apply ..).comp 0 (ray_smooth v h)).of_le le_top
  have origin:ray v 0=0:=by simp [ray]
  rw [motor,after_move]
  have hp:=gaze_cut (f:=fun t:ℝ=>f (t•oneRay)) _ (fixed_path oneRay f ok) 1
    (fun i hi=>by rw [Nat.lt_one_iff.mp hi,glimpse_coeff,paste_first];simp [f,origin,traceP])
  apply gaze_replace hp
  filter_upwards [eventually_pos] with t ht
  simp [f,ray,oneRay,Pi.smul_apply,smul_eq_mul,ht.ne']

theorem smooth (v:ℝ→Rays I)(h:ContDiffAt ℝ ω v 0)(p:Glyphs ℝ I):
    ContDiffAt ℝ ω (fun t=>traceP (v t) p) 0:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp only [traceP,MvPolynomial.aeval_C];exact contDiffAt_const
  | add p q hp hq=>simpa only [traceP,map_add] using hp.add hq
  | mul_X p i hp=>
    have coord:ContDiffAt ℝ ω (fun t=>v t i) 0:=(contDiffAt_apply ..).comp 0 h
    simpa only [traceP,map_mul,MvPolynomial.aeval_X] using hp.mul coord

/-- One formal substitution tests precisely the finite real jet along
the field curve, including all lower coupling grades. -/
theorem coefficient (W:Pap I)(v:ℝ→Rays I)(h:ContDiffAt ℝ ω v 0)(k:ℕ):
    coeff k (glimpse oneRay (roam ℝ (motor (ray v)) W))=
    weigh v (evaluation W) k:=by
  rw [glimpse_slide]
  let z(i:I):=glimpse oneRay (motor (ray v) i)
  change coeff k (fog (insertAt ℝ z) W)=_
  rw [fog,coeff_mk,weigh]
  apply Finset.sum_congr rfl
  intro j hj
  have lower:j≤k:=Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [coeff_mul_X_pow',if_pos lower]
  let f(t:ℝ):=traceP (v t) (coeff j W)
  have priced:=gaze_path v z (coeff j W) (coordinate v h)
  have same:=Aspiration.unique priced (needed (smooth v h (coeff j W)))
  exact congrFun same (k-j)

end YM.Integration.WilsonFormalGaugeCurve
end
