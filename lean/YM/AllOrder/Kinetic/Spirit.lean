import YM.AllOrder.Kinetic.Connect
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
variable (e:rule α n≃L[ℝ]X)(v:rule β n≃L[ℝ]Y)
local notation "L"=> (α⊕β)
local notation "I"=> Leaf n L
local notation "E"=> X×Y
local notation "I'"=> Leaf n β
section shift
lemma pivot (M₀:X→L[ℝ]Y) (f:Y→ℝ)(x:X)(h:ContDiffAt ℝ ω f 0) (k:ℕ): Radial.jet (f ∘ M₀) k x= Radial.jet f k (M₀ x):= by rw [jet, Next.Foundations.jets_linear M₀ (h.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl
-- allow exact equality via analytic title F,H. keep hJ rank arbitrary.
variable (A : X×Y→ℝ)(ρ:X→Y)(G:X×Y→ℝ)(h:Steered A ρ)
variable (H:ℝ×(X×Y)→ℝ)(hb:ContDiffAt ℝ ω G 0)
variable [DecidableEq α][DecidableEq β]
local notation "u"=> fderiv ℝ ρ 0
local notation "O'"=> posture e v
variable (U:Stalk (α⊕β) (α⊕β))(V:Stalk β β)(hV:Belt V a D)(hU:Belt U a C)(hA:0≤a)(hD:0≤D)(he:direct V n=(pulse e v A)⁻¹)(hx:direct U n=mail e v A)
def ponant (A:X×Y →ℝ)(ρ:X→Y)(H:ℝ×(X×Y)→ℝ):= Impulse (fderiv ℝ ρ 0) (A ∘ Prod.snd) H
include hU hV he hx h hA hD
lemma minimum (k:ℕ) (X₀:rule α n) : liftQ A u (e X₀)= Radial.jet (A∘ O') 2 (turn U V (mingle X₀ 0)):= by
    rw [show A ∘ O'= A ∘ (O').toContinuousLinearMap from rfl,pivot _ A _ h.hard]; change _ = jet A _ (O' _); rw [arranged e v A ρ h U V he hx hU hV hA hD,_root_.map_zero, add_zero]; rfl
lemma luna (x:rule L n) : O' (turn U V x)= (colorful u (O' x)).2:= by
 conv_lhs => arg 2; rhs; rw [← pair_mingle x]
 rw [arranged e v A ρ h U V he hx hU hV hA hD]; rfl
include hb in
lemma roses (c:ℝ)(hF:∀ x:ℝ×(X×Y),Real.log (H x)=c-G x.2) (k:ℕ)(hk:k≠0): (ponant A ρ H k) ∘ O'= (((-1:ℝ) • Radial.jet (A∘ O') (k+2))+ (-1:ℝ) • Radial.jet (G ∘ O') k) ∘ turn U V:= by
  funext x; let P':= turn U V x; let y:= O' x; let f:=Real.log ∘ H; let Q:=ContinuousLinearMap.snd ℝ ℝ (X×Y); let A':= A ∘ Q; let G':= G ∘ Q; let t:= colorful u y
  have h':∀ r:ℕ, r≠0→ jet f r t= -(jet G' r t):= by
     intro r hr; let v: ℝ×(X×Y)→ℝ:=fun _=>c; have hv : f=v-G':= funext hF; rw [hv]; unfold jet; have hG:ContDiffAt ℝ ω G' 0:= (ContDiffAt.comp (g:=G) (f:=Q) _ ((map_zero Q).symm ▸ hb) Q.contDiff.contDiffAt)
     rw [iteratedFDeriv_sub_apply ((show ContDiffAt ℝ ω v 0 from contDiffAt_const).of_le le_top) (hG.of_le le_top)]; simp [v, hr, iteratedFDeriv_const_of_ne hr]
  unfold ponant Impulse; simp only [Function.comp_apply, win_atn _ hk,token, Pi.sub_apply,spine, Pi.add_apply, Pi.smul_apply, add_zero, neg_one_smul];
  rw [show jet (Real.log ∘ H) k _= -jet G' k t from h' k hk];
  change -(jet (G ∘ Q) k t)- jet A' (k+2) t= -jet (A ∘ (O').toContinuousLinearMap) _ P'+ -jet (G ∘ (O').toContinuousLinearMap) k P'
  rw [pivot Q G t hb,pivot Q A t h.hard,pivot _ A P' h.hard,pivot _ G P' hb]; rw [show Q t= O' P' from (luna e v A ρ h U V hV hU hA hD he hx x).symm]; abel_nf; rw [add_comm]; rfl -- reorder abel
end shift
end YM.AllOrder.Kinetic
