import YM.PertExtension.AirPairing
import YM.PertExtension.OrbPolarization

/-! Wilson tree-hessian pairing of curl outputs, full torus projection plus its
inversion image. Exact, before the coupling and spacing limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.PertExtension.LatticePT.Projection
open Function Lattice Air Orbit Band Orb GaussianScore LinearMap
open scoped Classical Topology BigOperators RealInnerProductSpace
variable {G : Gauge}{n:Side}

def glare (p:FaceAt n) (ξ:G.Color) : SheetLink G n:=fun e=>(shining p e).re • ξ
lemma crease_glare (y ξ)(z:FaceAt n) : crease G (glare y ξ) z=(disk (shining y) z).re • ξ:= by unfold crease glare disk Curl;rw [Complex.sub_re,Complex.sub_re,Complex.add_re,sub_smul,sub_smul, add_smul]
lemma costate_shine (y:FaceAt n)(ξ:G.Color): Costates (glare y ξ) y ξ:= by
   intro A
   let B(e:Edge (Site n)):ℂ:=↑(inner ℝ ξ (A e):ℝ)
   have hb p : disk B p=(↑(inner ℝ ξ (crease G A p)):ℂ):=by unfold disk B crease Curl; rw [inner_sub_right,inner_sub_right,inner_add_right]; push_cast;rfl
   let H:=disk (shining y)
   let F(p):=H p * inner ℝ ξ (crease G A p)
   have ht p : (F p).re=(H p).re * inner ℝ ξ (crease G A p) :=by simp [F,Complex.mul_re]
   have h:=scalar_law B y
   simp_rw [hb] at h
   have hr : (∑ p, (F p).re)=inner ℝ ξ (crease G A y) := (Complex.re_sum _ F).symm.trans (congr_arg Complex.re h)
   calc
      _ = ∑ p:FaceAt n, (F p).re:= by refine Finset.sum_congr rfl fun i _=>?_ ; rw [crease_glare,ht,real_inner_smul_left]
      _ = _:=hr
variable (e:Even n.val)(x y:FaceAt n) (ξ η:G.Color)
theorem curl_covariance :
   (saddle (G:=G) e).wick (signal y ξ) (signal x η)= ((disk (shining y) x).re + (disk (shining y) (fold n x)).re)*inner ℝ η ξ:=by
   rw [wick_uses e _ _ _ _ _ (costate_shine y ξ),crease_glare,crease_glare, ←add_smul];exact inner_smul_right η ξ _
end YM.PertExtension.LatticePT.Projection
