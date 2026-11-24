import YM.FormalOPE.RG10.Boardwalk.Poi
/-!
 # Precise reconstruction of Stock's orientation branch budgets
No need positive raw coefficient limits: use finite order arrays with stationarity ONLY at
leading & diagnostic locations. Even if the leading answer differs at each mesh, selecting
Stock's specified solver on both fibers preserves power budget, when both converge to same
 given regular baseline and the drift between them is fast [pointwise in each fixed test list,
with same l filter]. On other coordinates paid separately, no assumption on variable layouts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Lawn
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle
open scoped Topology BigOperators Classical ContDiff
variable {I T J : Type*}{l:Filter I}{r n :ℕ}
variable {P:Path l}
variable [Fintype J]{a:T→ℕ}{D:TestSystem J T a}
local notation "Φ"=>Mark J a
local notation "σ"=>D.Z
local notation "Π'"=>D.Parameter
-- no positive limit asked (might blow with logs of the shared coupling conversion)
variable {w: Mark J a→ℝ}{x y : I→ Mark J a→fps}
abbrev scale (w:Mark J a →ℝ)(x:Mark J a→fps):= D.leadingAdjust w (fun i=>constantCoeff (x i))
local notation "U" i =>scale (D:=D) w (x i)
local notation "V" i =>scale (D:=D) w (y i)
def dial (D:TestSystem J T a) (x:Mark J a→fps):=fun i=>constantCoeff (x (markIn D.tests i))
local notation "C" i => dial D (x i)
local notation "B" i => dial D (y i)
variable (hP : D.Regular w)
variable (he:Tendsto (fun i=> dial D (x i)) l (𝓝 (w ∘ markIn D.tests)))
include hP he
lemma position_pair : Tendsto (fun i=> (dial D (x i), D.branch w (dial D (x i)))) l (𝓝 (w ∘ markIn D.tests, (0:D.Z))):= (D.tends w hP).comp he

private def vane (u: D.Parameter × D.Z): D.Z →L[ℝ] D.Z := (ContinuousLinearMap.snd ℝ Π' σ).comp ((fderiv ℝ D.solver u).comp (ContinuousLinearMap.inr ℝ Π' σ))
-- computable after fixing raw diagnostics
local notation "J'" i => (C i, D.branch w (C i))
local notation "S"=> w ∘ markIn D.tests
local notation "Ω"=> LinearMap.toContinuousLinearMap (D.inspect w)
def E (D:TestSystem J T a)(w:Mark J a→ℝ)(x:Mark J a→fps) : D.Z→ₗ[ℝ] D.Z:= (scale (D:=D) w x).inspect (fun t=>constantCoeff (x t))
def breathing (D:TestSystem J T a)(w:Mark J a→ℝ)(x:Mark J a→fps) : D.Z→L[ℝ] D.Z:= LinearMap.toContinuousLinearMap (E D w x)
local notation "δ" i=>breathing D w (x i)
def Rfix (D:TestSystem J T a) (w:Mark J a→ℝ)(x:Mark J a→fps) : D.Z→ₗ[ℝ] D.Z := (scale (D:=D) w x).repair x
omit hP he
private lemma shifts (i:I)(z:D.Z) : (fderiv ℝ D.solver (dial D (x i),D.branch w (dial D (x i)))) (0,z)=(0,(δ i) z):=
 D.shifted_deriv (fun p=>constantCoeff (x i p)) (b:= D.branch w (C i)) (scale (D:=D) w (x i)) z rfl rfl fun u p=> by
   change ((D.result (p ∘ markIn _) (D.baseline+ (u+_).val)).val)= (D.result _ _).val
   simp only [Submodule.coe_add,scale,TestSystem.leadingAdjust]; congr 2; abel
private lemma center : vane (S,(0:D.Z))=LinearMap.toContinuousLinearMap (D.inspect w):= ContinuousLinearMap.ext fun i=>congr_arg Prod.snd (D.solve_fderiv w i)
private lemma atVane (i:I): vane (C i, D.branch w (C i))= δ i := ContinuousLinearMap.ext fun u=> congr_arg Prod.snd (shifts i u)
private lemma regularOrigin : ContDiff ℝ ω (vane (D:=D)) := by
 let f:= fderiv ℝ D.solver; have h: ContDiff ℝ ω f:= (D.smooth_solve.fderiv_right (by simp)); exact contDiff_const.clm_comp (h.clm_comp contDiff_const) -- inspect
include hP he
theorem opens : ∀ᶠ i in l,(scale (D:=D) w (x i)).Regular (fun t=>constantCoeff (x i t)):= by
 filter_upwards [he.eventually (D.solves w hP),(position_pair hP he).eventually (D.eventually_fullrank w hP)] with i hi h
 refine ⟨hi,?_ ⟩; have h := h.injective; -- injectivity of fderiv
 let ft:=fderiv ℝ D.solver (J' i); have h:Injective ft:= h; let A:= E D w (x i); have ht: Injective A:= fun (u v:D.Z) hh=>congr_arg Prod.snd (h (show ft (0,u)=ft (0,v) from by unfold ft; rw [shifts i u,shifts i v]; exact congr_arg ((_,·)) hh)) -- inspect
 exact ⟨ht,LinearMap.injective_iff_surjective.mp ht⟩

lemma sizing : Tendsto (fun i => breathing D w (x i)) l (𝓝 (LinearMap.toContinuousLinearMap (D.inspect w))) := by
 simp_rw [← center,← atVane]; exact (regularOrigin (D:=D)).continuous.continuousAt.tendsto.comp (position_pair hP he)
-- actual proof budgets
variable (hx: Fair P (fun i=> dial D (x i)) (fun i=>dial D (y i)))
include hx
private lemma branchMap : Fair P (fun i=> D.branch w (dial D (x i))) (fun i=> D.branch w (dial D (y i))):= by
 have hS := (D.eventually_fullrank w hP).self_of_nhds; simp_rw [TestSystem.branch,dif_pos hS]
 let F:= fderiv ℝ D.solver (S,(0:D.Z))
 have ht : D.solver (S,(0:D.Z))=(w ∘ markIn D.tests,D.target) := Prod.ext rfl (by simpa [TestSystem.solver,TestSystem.lieResult] using hP.fits)
 let Q := LinearEquiv.ofBijective F.toLinearMap hS; have hr : HasStrictFDerivAt D.solver Q.toContinuousLinearEquiv.toContinuousLinearMap (S,(0:D.Z)):= D.smooth_solve.hasStrictFDerivAt (by simp)
 have hB:= hr.to_localInverse (f':=Q.toContinuousLinearEquiv); rw [ht] at hB
 exact ((hx.pairing (Fair.fixed D.target)).press hB (he.prodMk_nhds tendsto_const_nhds)).map (ContinuousLinearMap.snd ℝ Π' σ)
lemma baseline : Fair P (fun i=> (scale (D:=D) w (x i)).baseline) (fun i=>(scale (D:=D) w (y i)).baseline):= (Fair.fixed D.baseline).join ((branchMap hP he hx).map D.Z.subtypeL)
lemma derivative : Fair P (fun i=> breathing D w (x i)) (fun i=> breathing D w (y i)) := by
 simp_rw [← atVane]; exact (hx.pairing (branchMap hP he hx)).press (regularOrigin.hasStrictFDerivAt (by simp)) (position_pair hP he)
lemma inverse : Fair P (fun i=> Ring.inverse (δ i)) (fun i=>Ring.inverse (breathing D w (y i))):= (derivative hP he hx).invert (ContinuousLinearMap.isUnit_iff_bijective.mpr hP.rank) (sizing hP he)
omit hx
lemma review (p:I→D.Z) : ∀ᶠ i in l,Rfix D w (x i) (p i) = Ring.inverse (δ i) (p i):= by
 filter_upwards [opens hP he] with i hi;
 have hh : Function.Bijective (breathing D w (x i)):= hi.rank
 refine hh.injective (show (δ i) _=(δ i) _ from ?_);
 rw [show (δ i) (Ring.inverse (δ i) (p i))=p i from DFunLike.congr_fun (Ring.mul_inverse_cancel (δ i) (ContinuousLinearMap.isUnit_iff_bijective.mpr hh)) (p i)]
 change (TestSystem.inspect (scale (D:=D) w (x i)) _) ((scale (D:=D) w (x i)).repair (x i) (p i))= p i
 rw [TestSystem.repair, dif_pos hi.rank]
 exact (LinearEquiv.ofBijective _ hi.rank).apply_symm_apply _
include hx
lemma repair {p q:I→D.Z}(hk:Fair P p q) : Fair P (fun i=> Rfix D w (x i) (p i)) (fun i=>Rfix D w (y i) (q i)) := (hk.inspect (inverse hP he hx)).fit ((review hP he p).mono fun _ hi=> hi.symm) ((review hP (x:=y) (hx.both _ he) q).mono fun _ hi=> hi.symm) -- probably param x
end YM.FormalOPE.RG10.Boardwalk.Lawn
