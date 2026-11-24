import YM.RG11Proof.Stress.Surface
import YM.Pert.Lifted
import YM.UVNext.FREE_STRESS_CERTIFICATE.Certificate

/-!
# Free rank of normalization tests

Divergence pivots and a translation signal about the same camera. This
uses precisely d≤4 stress, probes at fixed engineering one, release Maxwell
certificate plus translation flux proof at free AND sign adapter between two
canonical stress APIs, not a color-blind Gram assumption on a redundant
stress family. No constant term in KernelSpace; for the comparison
**retain** exact chosen vacuum stress separately (unobservable here).
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.RG11.Stress
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius BigOperators
open Maxwell Labels Table Climb Work.A01 Next.UVStress UVNext.FreeStress Function Filter MeasureTheory Analysis Pert.Position
variable {G:Gauge}(F:Frames G)(hG:G.Simple)

def cape (i j:Axis):Fin 1→ E F 4:=fun _=> flat F i j i j

-- word interfaces for homogeneous degree 4 tags (don't require grade 4)
def fourWord {n}(v : Fin n→ E F 4):Fin n→(freeTable F).Tag:=Sigma.mk 4 ∘ v

def site {n}(v:Fin n→ E F 4):Points n→ℂ:=fun y=>visible F 4 y v

@[simp] theorem site_desc {n}(v:Fin n→ E F 4)(x:Points n):site F v x=(freeTable F).useAt (freeTable F) x (fourWord F v):=rfl
@[simp] theorem word_succ {n}(v:E F 4)(k:Fin n→E F 4):fourWord F (Fin.cons (α:=fun _ : Fin (n+1)=> E F 4) v k)=Fin.cons ⟨4,v⟩ (fourWord F k):=comp_cons ..

@[simp] theorem cape_desc (i j:Axis): fourWord F (cape F i j)=negs F i j i j:=by
  rfl

-- χ can be fixed any admissible annular test about x
include hG in
 theorem ignites {χ:E4→ℝ}(hχ:Window (camera 0) χ)
     (J:KernelSpace (Free.spin_free F))
     (hd:∀ (w:Fin 1→E F 4), (∑ a:Axis, Points.gradient (n:=2) 0 a (site F (Fin.cons (α:=fun _:Fin 2=> E F 4) (J.val a 0) w)) (camera 0))=0)
     (hf:∀ (w:Fin 2→E F 4), (∑ a:Axis,-∫ y:E4,((D (basis a) χ y:ℝ):ℂ)*site F (Fin.cons (α:=fun _:Fin 3=>E F 4) (J.val a 0) w) (Points.cons y (camera 0)))=0):
     J=0:=by
  let H:= Free.spin_free F
  let W:= Free.scheme F
  have ho := Free.phase_orientation F
  have hx(k i j a:Axis)(p): Points.gradient (n:=2) 0 a (site F (Fin.cons (α:=fun _:Fin 2=>E F 4) p (cape F i j))) (camera k)=hearing F (camera k) i j i j 5 (W.deriv 4 a p):=by
    rw [show site F (Fin.cons (α:=fun _:Fin 2=>E F 4) p (cape F i j))=(fun y=>(freeTable F).useAt (freeTable F) y (Fin.cons (α:=fun _=> (freeTable F).Tag) ⟨4,p⟩ (negs F i j i j))) from funext fun _=>by rw [site_desc,word_succ,cape_desc],listens]
    exact ((Free.scheme_derives F).kernels 4 a _ (shutter k) _).symm
  have hJ : currentDiv W H ho J=0:=by
    apply (scope_exact F H hG W (Free.scheme_derives F) ho).1; rw [map_zero]; apply Prod.ext
    all_goals -- evaluate switch microphones
      change Complex.re (((loud G)⁻¹:ℂ)* ((hearing F (camera 0) _ _ _ _ 5) (∑ i:Axis,W.deriv 4 i (J.val i 0))))=0
      rw [map_sum]
      simp_rw [← hx]; rw [hd,mul_zero]; rfl
  let j : LinearMap.ker (currentDiv W H ho):= ⟨generator F H, radiating F H hG W (Free.scheme_derives F) ho⟩
  have he:j≠0:=fun h=>generator_nonzero F H hG (congrArg Subtype.val h)
  obtain ⟨c,hc⟩: ∃ c:ℝ, c • j=⟨J,hJ⟩:= (finrank_eq_one_iff_of_nonzero' j he).1 (line_dim F H hG W (Free.scheme_derives F) ho) ⟨J,hJ⟩
  -- easier J= c * original
  have hz: c • Free.original F=J.val:=by
    rw [←Pert.common_stress,torch,one_smul,←lighting F H]
    exact congrArg (fun z:LinearMap.ker (currentDiv W H ho)=>z.val.val) hc
  let k:=flat F 0 1 0 1
  have beam:= (Free.beacon_signal F c).translation (shutter 0) (fourWord F (cape F 0 1)) hχ 0 4 k
  rw [hz] at beam
  rw [show shellGrad (freeTable F) J.val χ 0 (camera 0) (fourWord F (cape F 0 1)) k=
      ∑ a:Axis,-∫ y:E4,((D (basis a) χ y:ℝ):ℂ)*site F (Fin.cons (α:=fun _:Fin 3=>E F 4) (J.val a 0) (Fin.cons (α:=fun _:Fin 2=>E F 4) k (cape F 0 1))) (Points.cons y (camera 0)) from by simp_rw [site_desc,word_succ,Finset.sum_neg_distrib]; rfl, hf,cape_desc, ← listens] at beam
  have hq : (-(c:ℂ))* (loud G * (-256:ℂ))=0:=by
    change (0:ℂ)=hearing _ _ _ _ _ _ _ ((-c:ℝ) • W.deriv _ _ _) at beam
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),_root_.map_smul] at beam
    unfold k at beam
    rw [listens_to F W (Free.scheme_derives F), show slide 0 0 0 1 0 1 0 1 0 1=(-256:ℤ) from by decide] at beam
    change (0:ℂ)=(((-c:ℝ):ℂ))* (loud G*(↑(-256:ℤ):ℂ)) at beam
    simpa only [Complex.ofReal_neg,Int.cast_neg,Int.cast_ofNat] using beam.symm
  suffices hh : c=0 by subst c; rw [zero_smul] at hc; exact (congrArg Subtype.val hc.symm)
  have hec:= (mul_eq_zero.mp hq).resolve_right (mul_ne_zero (loud_ne hG) (by norm_num))
  exact Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hec)
end YM.RG11.Stress
