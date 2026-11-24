import YM.RG11Proof.Fields.Predictions
import YM.RG11Proof.Scale.Portable
import YM.RG11Proof.Scale.TestEuler

/-!
# Formal Euler & scale convention adapters on the nested Yang--Mills basis

Confirm the free law incl exact weight & first Euler on this actual field
quotient. POINTwise (continuum), test all conf compact with Jacobian in Points n
adapter. Independent of which prescription eventually supplies perturbative
continuation, and NOT a proof at the common actual regulator.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.RG11.Fields
open scoped Classical BigOperators Topology ContDiff
open PowerSeries YM.RG11.Jets YM.RG11.Scale YM.PertExtension.Position
open MeasureTheory Function Set Filter Labels Maxwell Extra.FD
open YM.Pert.Position
variable {G:Gauge}{F:Frames G}

-- Concrete Euclid.Test dilation and infinitesimal generator
def narrow (u:ℝ) : Scale.Keeper form:= ⟨fun v=> ⟨form v,compress (form v) u v.test⟩,fun _=>rfl⟩
@[simp] theorem narrow_id : narrow 0= Scale.Keeper.id form:=by
  unfold narrow Scale.Keeper.id
  congr!
  next v=> cases v; simp

def scalesX : Scale.Keeper form:= ⟨fun v=> ⟨form v,blows _ v.test⟩,fun _=>rfl⟩

def height {d:ℕ}(B:Adapted F d): B.toBasis.J→ℕ:= fun i=>(B.w i).1

 theorem lift_permits {d:ℕ}(B:Adapted F d): Scale.Permits B.toBasis.J (height B) B.toBasis.guard:=
   (Scale.Permits.position (H:=B.toBasis.Hmat) (w:=height B) (fun s {_ _} he=>Basis.signed_pure B s (fun hh=>he (congrArg Prod.fst hh))) B.unitIndex).tests (by
     ext z; exact (exactGuard B z).symm)

private theorem pay (u:ℝ)(i:ℕ): ((↑(wide u):ℂ)^i)=(Real.exp (i*u):ℝ):=by
  simp only [wide,←Complex.ofReal_pow, Real.exp_nat_mul]

private theorem pay_b (u:ℝ)(i:ℝ):(Real.exp (i*(-u)):ℂ)*(Real.exp (i*u):ℂ)=1:=by
   rw [← Complex.ofReal_mul, mul_neg, Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero _),Complex.ofReal_one]

 theorem free_rays {d r}(B:Adapted F d)(u:ℝ){x:Points r}(hx:x∈conf r)(v:Fin r→B.toBasis.J):
    visible F d (wide (-u) • x) (B.b ∘ v)=(↑(Real.exp ((∑ i:Fin r,(height B (v i):ℝ))*u)):ℂ)*visible F d x (B.b ∘ v):=by
   have H (i:Fin r) : Extra.FD.Exact (writes F d (B.b (v i))) (height B (v i)) :=by
     intro z hz
     exact congrArg Prod.fst ((weight_collapse z).symm.trans ((B.alive (v i)) hz))
   have he:= YM.Pert.Scale.rising_moment (x:=x) (q:=fun i=> writes F d (B.b (v i))) (t:=wide (-u)) hx H (Real.exp_ne_zero _)
   rw [MultilinearMap.map_smul_univ,smul_eq_mul] at he
   simp only [writes_pair, Function.comp_apply]
   rw [← he,← mul_assoc]
   simp_rw [pay]
   have hp : (Real.exp ((∑ i:Fin r,(height B (v i):ℝ))*u):ℂ) * (∏ i:Fin r,(Real.exp ((height B (v i):ℝ)*(-u)):ℂ))=1:=by
     change _ * (∏ i:Fin r, Complex.ofRealHom (Real.exp ((height B (v i):ℝ)*(-u))))=1
     rw [← map_prod Complex.ofRealHom]
     rw [← Real.exp_sum,← Finset.sum_mul,mul_comm]; exact pay_b _ _
   rw [hp, one_mul]

 theorem scaled_free {d r}(B:Adapted F d)(u:ℝ)(f:Test r)(v:Fin r→B.toBasis.J):
     wickReading F d (compress r u f) (B.b ∘ v)=(Real.exp ((∑ i:Fin r,(height B (v i):ℝ))*u):ℂ)*wickReading F d f (B.b ∘ v):=by
   unfold wickReading; simp only [MultilinearMap.coe_mk]
   rw [reads_compress]; rw [f.apply_eq (fun _ hx=> free_rays B u hx v)]; unfold Test.applyTo
   dsimp only; simp_rw [mul_left_comm (_:ℂ) (Real.exp (_*u):ℂ),integral_const_mul]

 theorem engineering_zero {d}(B:Adapted F d)(v : point B.toBasis):
   (fun u:ℝ=>rowZero B.toBasis ((narrow u).move v))∈ Scale.beam (bulk (height B) v):=by
  let p:Fin (v.1.order)→E F d:=B.b ∘ v.2
  use Polynomial.C ((wickReading F d v.1.test p).re)
  intro u _; change (wickReading F d (compress _ u v.1.test) (B.b ∘ v.2)).re=_
  rw [scaled_free,Complex.re_ofReal_mul,Polynomial.eval_C]; rfl

 theorem level_anchor {d}(B:Adapted F d)(v:point B.toBasis):
    rowZero B.toBasis (scalesX.move v)= bulk (height B) v * rowZero B.toBasis v:=by
   let p:Fin (v.1.order)→E F d:=B.b ∘ v.2
   have he : HasDerivAt (fun u:ℝ=>wickReading F d (compress _ u v.1.test) p) (wickReading F d (blows _ v.1.test) p) (0:ℝ):= by
     have h:=GaugeEuler (visible_cont F d p) v.1.test 0; rw [compress_zero] at h; exact h
   let W:=bulk (height B) v
   have hf (k:ℝ): wickReading F d (compress _ k v.1.test) p=(↑(Real.exp (W*k)):ℂ)*wickReading F d v.1.test p:=scaled_free B k v.1.test v.2
   have hw : HasDerivAt (fun u:ℝ=>Real.exp (W*u)) W 0:=by simpa [Function.comp_def] using Real.hasDerivAt_exp (W*(0:ℝ)) |>.comp (h:=fun u=>W*u) 0 ((hasDerivAt_id' (0:ℝ)).const_mul W)
   have hb := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hw).mul_const (wickReading F d v.1.test p)
   simp_rw [hf] at he
   have ht := congrArg Complex.re (HasDerivAt.unique he hb); change _ = ((W:ℂ) * (wickReading F d v.1.test) p).re at ht; rw [Complex.re_ofReal_mul] at ht; exact ht
end YM.RG11.Fields
