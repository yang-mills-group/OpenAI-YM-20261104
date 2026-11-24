import YM.RG11Proof.Rigidity.Ice.Guarding
import YM.RG11Proof.Rigidity.Ice.Derived

/-!
# Differentiate along an actual color circle—not along a chosen lift of the
new frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD Reads Maxwell.Free Crowd Prism
open scoped Classical BigOperators InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color
local notation "Y" => V→L[ℝ] V

def spinY (a : V):Y:=(G.ad a).toContinuousLinearMap
def caravan (i : V)(s: ℝ):=G.lieExp (s • i)

lemma Feasible.compass {b:Buffer F d}{t:ℝ}{O:Wheel G}(hd : 6≤d)(h:Feasible b t (steers O))(u:G.El)(x y:V):
    let Q:= fun v : V=> O.symm (G.adjoint u (O v))
    G.ad (Q x) (Q y) = Q (G.ad x y) := by
  intro Q
  have hq : Surjective Q:=fun i=> ⟨O.symm (G.adjoint u⁻¹ (O i)),by unfold Q; rw [O.apply_symm_apply,← G.adjoint_mul,mul_inv_cancel]; simp⟩
  apply ext_inner_left ℝ; intro z; obtain ⟨i,rfl⟩:=hq z
  change tri (Q i) (Q x) (Q y) = _
  rw [show tri _ _ _=_ from h.trio hd u i x y, show inner ℝ (Q i) (Q (G.ad x y)) = inner ℝ i (G.ad x y) from
    (O.symm.inner_map_map ..).trans ((adSpin_iso u ..).trans (O.inner_map_map ..))]; rfl

private lemma derives_comp (O:Wheel G)(H : ∀ (u:G.El)(x y:V), let Q:=fun v=> O.symm (G.adjoint u (O v));G.ad (Q x) (Q y)=Q (G.ad x y)) (i:V):
    Derives (((steers O.symm).comp ((spinY i).comp (steers O))).toLinearMap):=by
  intro x y
  let P (s : ℝ)(x : V):= O.symm (G.adjoint (caravan i s) (O x))
  let D:= (steers O.symm).comp ((spinY i).comp (steers O))
  have he (x) : HasDerivAt (fun s=> P s x) (D x) 0 :=
    (steers O.symm).hasFDerivAt.comp_hasDerivAt _ (adj_has i (O x))
  let A : V→L[ℝ] V→L[ℝ] V:= (LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad).toContinuousLinearMap
  have hm:= ((A.hasFDerivAt.comp_hasDerivAt _ (he x)).clm_apply (he y))
  have hf (x) : P 0 x=x:= by simp [P,caravan]
  simp_rw [hf] at hm
  have hh := he (G.ad x y)
  simp_rw [← show ∀ s,A (P s x) (P s y) = P s (G.ad x y) from fun s=> H (caravan i s) x y] at hh
  have hx:=hh.unique hm
  simp_rw [Function.comp_apply,hf] at hx
  exact hx

lemma Feasible.carriage {b:Buffer F d}{t:ℝ}{O: Wheel G}(hd : 6≤d)(hG:G.Simple)(h:Feasible b t (steers O))(i:V):
    ∃ r:V,(steers O.symm).comp ((spinY i).comp (steers O))=spinY r :=by
  obtain ⟨r,hr⟩:=(derives_comp O (h.compass hd) i).lift hG
  exact ⟨r,ContinuousLinearMap.ext (fun x=> LinearMap.congr_fun hr x)⟩

lemma Feasible.folds {b:Buffer F d}{t:ℝ}{O:Y}(h:Feasible b t O):∃ v:Wheel G,O= steers v:=by
  let f:= O.toLinearMap
  have ht (x) : ‖O x‖=‖x‖:= by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [← real_inner_self_eq_norm_sq,h.1]
  let v: V→ₗᵢ[ℝ] V:=⟨f,ht⟩
  let B := LinearEquiv.ofBijective f ⟨v.injective,LinearMap.injective_iff_surjective.mp v.injective⟩
  exact ⟨{B with norm_map':=ht},ContinuousLinearMap.ext fun _=>rfl⟩
end YM.RG11.Rigidity.Ice
