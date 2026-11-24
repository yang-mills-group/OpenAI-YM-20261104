import YM.RG17.Reports
import YM.Trace2.Shear
import YM.Work.A05.Window

/-!
Smear the shear system instead of postulating *pointwise* derivative
rates from merely separated testing. Conservativity in physical labels,
at real r. Signs use RG13 κ and Wick/free metric0 normalization.
All Ward tests are at separated finite shapes. No puncture-limit claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open Points Analysis Work.A05 Trace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{B:Register G} {f:Extraction.Order}{S:Table B} {n:ℕ}(r:ℝ)
-- arbitrary table capture for this step, free included

def plate {d:Fin n→ℕ}(v:Labels S d)(r:ℝ)(ψ:Test n) := ψ.applyTo (fun x=> S.useAt S (r•x) (Orbits.tags v))
lemma plate_value {d:Fin n→ℕ}(v:Labels S d)(T:Table B)(ht:T.Hierarchy) {x:Points n}(hx:x∈ conf n) {r:ℝ}(hr:0<r):
    S.useAt T (r•x) (Orbits.tags v)= Orbits.moment T (posed r x) v:=by
    let y:= r•x
    have hy:= Work.A05.smul_conf hr hx
    rw [observed, show posed r x=y.ofLp from rfl, named_fin T ht.laws.toSymmetric _ hy]; rfl
lemma plate_int {d:Fin n→ℕ}(v:Labels S d)(h:S.Hierarchy) (ψ:Test n) {r:ℝ}(hr:0<r) :
   Integrable (fun x:Points n=> ψ x * S.useAt S (r•x) (Orbits.tags v)):=
    ψ.smearing ((S.class_smooth S h.smooth (Orbits.tags v)).continuousOn.comp (show Continuous (fun x:Points n=> r•x) by fun_prop).continuousOn (fun _ hx=> smul_conf hr hx))
def bilim (x:Points 2)(p q:S.Field 4) := S.useAt S x (Fin.cons ⟨4,p⟩ (fun _:Fin 1=>⟨4,q⟩))
def derym (x:Points 2)(i:Axis)(p q:S.Field 4):= gradient 0 i (fun x=> bilim x p q) x
lemma pair_plate (x y:S.Field 4) (ψ:Test 2): plate (S:=S) (d:=fun _=>4) ![x,y] r ψ= ψ.applyTo (fun t:Points 2=> bilim (r•t) x y) := by
    unfold plate bilim; congr 1; funext t; congr 1; funext i; fin_cases i <;> rfl
lemma physicalPlate {S:Table C.book} (F:Final C f S){d:Fin n→ℕ}(v:Labels S d) (ψ:Test n) {r:ℝ}(hr:0<r) : plate v r ψ= measured F v r none ψ:=ψ.apply_eq (fun _ hx=> plate_value v _ F.room.kernel hx hr)

-- `⊤` for Test means? check WithTop ℕ∞ versus ∞
def direct (i:Axis) (ψ: Test (n+1)): Test (n+1):=
    ⟨gradient 0 i ψ, by
        have h:=ψ.contDiff
        change ContDiff ℝ ∞ (fun x=> fderiv ℝ ψ x _)
        exact (h.fderiv_right (by simp)).clm_apply contDiff_const,
      ψ.hasCompactSupport.fderiv_apply ℝ _,
      subset_trans (tsupport_fderiv_apply_subset ℝ _) ψ.tsupport_subset⟩

section Grad
variable (x y:S.Field 4) {r:ℝ}(hr:0<r) (i:Axis)
include hr
lemma dualSmooth (h:S.Hierarchy) : ContDiffOn ℝ ∞ (fun a:Points 2=> bilim (r•a) x y) (conf 2):=
    (S.class_smooth S h.smooth _).comp (show ContDiff ℝ ∞ (fun a:Points 2=> r•a) by fun_prop).contDiffOn (fun _ hv=>smul_conf hr hv)

def swipe (r:ℝ) (x y:S.Field 4) (i:Axis) (z:Points 2):ℂ := r • derym (r•z) i x y
set_option maxHeartbeats 600000 in
lemma reduceSwipe (h:S.Hierarchy) {z:Points 2}(hz:z∈conf _): swipe r x y i z= gradient 0 i (fun a:Points 2=> bilim (r•a) x y) z:=by
    let m(t:Points 2):= bilim t x y
    have ht:= smul_conf hr hz
    have hv:DifferentiableAt ℝ m (r•z):= ((S.class_smooth S h.smooth _ _ ht).contDiffAt ((conf_open _).mem_nhds ht)).differentiableAt (by simp)
    exact (Work.A04.gradient_scaled r m z hv 0 i).symm
lemma swipe_cont (h:S.Hierarchy) : ContinuousOn (swipe r x y i) (conf 2):=by
    apply ContinuousOn.congr (f:=gradient (n:=2) 0 i (fun z=> bilim (r•z) x y)) (fun z hz=> ?_ ) (fun z hz=> reduceSwipe x y hr i h hz)
    have hp:= ((dualSmooth x y hr h) z hz).contDiffAt ((conf_open 2).mem_nhds hz)
    exact ((dSmooth (m:=∞) hp (direction (n:=2) 0 i) (by simp)).continuousAt).continuousWithinAt
lemma sift (h:S.Hierarchy) (ψ:Test 2) : ψ.applyTo (swipe r x y i) = -plate (S:=S) (d:=fun _=>4) ![x,y] r (direct i ψ) := by
    let m(z:Points 2) := bilim (r•z) x y
    rw [← show ψ.applyTo (gradient 0 i m) = _ from (ψ.apply_eq (fun a ha=> reduceSwipe x y hr i h ha)).symm, pair_plate]
    have hx:=dualSmooth x y hr h
    have he:ContinuousOn (gradient 0 i m) (conf 2):= (swipe_cont x y hr i h).congr (fun z hz=> (reduceSwipe x y hr i h hz).symm)
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ((direct i ψ).smearing hx.continuousOn) (ψ.smearing he) (ψ.smearing hx.continuousOn) (fun z _=> ψ.contDiff.differentiable (by simp) z) (fun z hz=>(hx.contDiffAt ((conf_open _).mem_nhds (ψ.tsupport_subset hz))).differentiableAt (by simp))
end Grad

section Ray
variable {S:Table C.book} {F:Final C f S} (L:Layout F)
-- P4 actual; Ward-facing Layout convention needed
abbrev portal (L:Layout F) : Portrayal4 S:= L.frame 4
set_option quotPrecheck false
local notation "P"=>portal L
abbrev force (U:Portrayal4 S)(ψ:Test 2) (r:ℝ) (w:S.Field 4) := ψ.applyTo (swipe r (scalarRay U r) w timeAxis)
abbrev shiftPair (U:Portrayal4 S)(i:Axis)(ψ:Test 2)(r:ℝ) (w:S.Field 4) := ψ.applyTo (swipe r (tensorRay U r i timeAxis) w i)
noncomputable def shiftAll (U:Portrayal4 S)(ψ:Test 2)(r:ℝ)(w:S.Field 4):= ∑ i:Axis, shiftPair U i ψ r w
lemma swept (ψ:Test 2) {r:ℝ}(hr:0<r) {a b k} (h:Trace.StressRay F (P r) r a b k) (w:S.Field 4) :
    a • shiftAll P ψ r w+b • force P ψ r w=0:=by
    let t(i:Axis):=swipe r (tensorRay P r i timeAxis) w i; let z:=swipe r (scalarRay P r) w timeAxis
    have hp i:ContinuousOn (t i) (conf 2):= swipe_cont _ _ hr _ F.room.kernel
    have hv i:=ψ.smearing (hp i)
    let X x:=∑ i:Axis,ψ x*(t i x); let Y x:= ψ x * z x
    have hz: Integrable Y:= ψ.smearing (swipe_cont _ _ hr _ F.room.kernel) -- args
    have hx: Integrable X:= MeasureTheory.integrable_finsetSum _ (fun i _=>hv i)
    change a • (∑ i:Axis,∫ x:Points 2, ψ x*t i x)+ b • (∫ x:Points 2,Y x)=0
    rw [← MeasureTheory.integral_finsetSum _ (fun i _=>hv i)]; change a • (∫ x:Points 2, X x)+_= _
    rw [← MeasureTheory.integral_smul, ← MeasureTheory.integral_smul]
    change (∫ x:Points 2,(a • X) x)+(∫ x:Points 2,(b • Y) x)=0
    rw [← MeasureTheory.integral_add (hx.smul a) (hz.smul b)]
    refine Eq.trans (integral_congr_ae (μ:=volume) (g:=0) (Eventually.of_forall fun x=>?_)) (integral_zero ..)
    change a • X x+b • Y x=0
    by_cases he:x∈ conf _; swap
    · simp [X,Y,ψ.vanishes he] -- name
    have hq:=Trace.divergence_system F P h w (r•x) (smul_conf hr he) timeAxis
    rw [Finset.smul_sum] at hq
    change a • (∑ i:Axis,t i x)+ b • z x=0 at hq
    unfold X Y; rw [← Finset.mul_sum]; calc
         _ = ψ x * (a • (∑ i:Axis,t i x) + b • z x) := by rw [Complex.real_smul,Complex.real_smul,Complex.real_smul,Complex.real_smul]; ring
         _ = _ := by rw [hq,mul_zero]
end Ray
end YM.RG17
