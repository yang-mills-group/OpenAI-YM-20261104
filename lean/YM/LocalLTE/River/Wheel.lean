import YM.LocalLTE.River.Studio
/-! Genuine orbit portraits. Postprojection transforms move this exact Frame and charge
the FULL regular currency on covariantly moved supports.Y.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox FrameBox.Hall AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom Motion
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n κ:Side}{p:BudgetPoint}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{D:SectionData F}{R:Rep G n}{k v a u u' s t e x y z:ℝ}{m ℓ j:ℕ}{i:Site n}
local notation "Xp"=> Config G n→ℂ
open Next.Foundations Push.AbsoluteSums Animals
variable {L:Support n}
variable (r:Extra.Histories.Motion)
local notation "c'"=> r.fst
set_option quotPrecheck false
lemma paces (h:D.Sound A) (b: F.Coeff): dance r (presented D (0:Site n) t b)= presented D (0:Site n) t (Motion.patch F r b):=by
    let ξ:= (0:Site n); have he : ξ= affine c' ξ ξ:= by simp [ξ,Lattice.affine];
    have ht V: presented D ξ t b (pull c' ξ V) = presented D ξ t (F.act r.1.ortho b) V:=by
        change D.places (F.scaled t⁻¹ b) _ _=D.places _ ξ _; rw [D.placed_signed h, ← he, F.scaling]
    funext V; unfold dance Motion.patch Motion.scalar; rw [ht]; split; next hZ=>
       change _=D.places (F.scaled t⁻¹ (star _)) _ _; rw [scaled_star]; exact (h.ordinary_real ..).symm
    rfl
local notation "q0"=> turnSites r.1 (0:Site n)
local notation "Z'"=> L.image q0
noncomputable def rotationP (F:Labels.Frame G d)(n p:ℕ):=turnCost n p*Motion.orbitCost F
lemma turn_one (n p:ℕ):1 ≤ turnCost n p:=by unfold turnCost; exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
lemma rotation_one (n p:ℕ):1 ≤ rotationP F n p:= one_le_mul_of_one_le_of_one_le (turn_one ..) (orbitCost_one_le _)
lemma rotation_price (n p:ℕ):turnCost n p ≤ rotationP F n p ∧ orbitCost F ≤ rotationP F n p:=by
    exact ⟨le_mul_of_one_le_right (zero_le_one.trans (turn_one ..)) (orbitCost_one_le _),le_mul_of_one_le_left (zero_le_one.trans (orbitCost_one_le _)) (turn_one ..)⟩
local notation "s'"=> rotationP F p.order p.power
variable {f:Config G n→ℂ}
lemma priceMove (F:Labels.Frame G d) (h:p.Regular L f)(ht:p.supBounds 0 L f u):p.Regular (Z') (dance r f) ∧ p.supBounds 0 (Z') (dance r f) (rotationP F p.order p.power*u):=by
    have hF:= regular_pull h c' 0; have hU:=bound_pull h ht c' 0; rw [show turnSites c' (0:Site n) 0 = 0 from (show Lattice.affine c' (0:Site n) 0=0 from by simp [affine])] at hU
    let g:=rotationP F p.order p.power; have hx:p.supBounds 0 (Z') (f ∘ pull c' 0) (g*u):= bound_weaken hU (mul_le_mul_of_nonneg_right (rotation_price ..|>.1) ht.1)
    unfold dance Motion.scalar; split_ifs; next h=> exact ⟨regular_bar hF, bound_bar hF hx⟩
    exact ⟨hF,hx⟩
lemma Canvas.orbit (h:Canvas D k ℓ m p L f u)(hζ:p.Regular L f)(hD:D.Sound A)(hr:ConnectedActivityE6.Reliable G k v): Canvas D k ℓ m p (Z') (dance r f) (rotationP F p.order p.power*u):=by
    refine ⟨priceMove r F hζ h.value|>.2,fun hf=>?_⟩; obtain ⟨hX,g,hG,hV,⟨x,hx,hF⟩,j,hj,X,hb⟩:= h.analytic (fun h=>hf (by rw [h]; funext i; unfold dance Motion.scalar; split<;>simp))
    have hL : affine r.fst (0:Site n) 0=0:=by simp [affine]
    have he : ((neighbors ℓ (0:Site n)).image q0)=neighbors ℓ 0:=by
       apply Scarf.normRange (s:=⟨r.1,0⟩) hL.symm ℓ -- order? check
    let c:ℕ:=0 -- remove
    let y:= dance r g; obtain ⟨hY₁,hY₂⟩:=priceMove r F hG hV
    let V:=Motion.patch F r x; have hc:F.coeffSize V ≤ s'*u:= le_trans (patch_cost ..) (mul_le_mul (rotation_price ..|>.2) hx (Work.G08.size_nonneg ..) (zero_le_one.trans (rotation_one ..)))
    have hl : dance r f=y + presented D (0:Site n) p.threshold V:= by rw [← paces r hD,hF]; funext i; exact Motion.scalar_add ..
    let X' : Grove (affine c' (0:Site n) 0):= Hall.transplanted r.1 0 X
    let W : Grove (0:Site n):=by rw [hL.symm]; exact Hall.transplanted r.1 0 X
    refine ⟨(Finset.image_subset_image hX).trans he.le, y,hY₁,hY₂, ⟨_,hc,hl⟩,j,hj,W,fun i=>?_⟩
    have hi b:Replicated W j k (m+1) ((Port.scaleQ b ∘ g)∘pull c' (0:Site n)):= translatedPoly (s:=⟨r.1,0⟩) X j hL.symm hr (hb b) -- edit ▸ he reducibility
    by_cases hl:r.2=true
    · let uζ:ℝ:= if i then -1 else 1; rw [show Port.scaleQ i ∘ y=uζ • ((Port.scaleQ i ∘ g)∘pull c' 0) from (by funext x; cases i <;> simp [dance,Port.scaleQ,hl,y,uζ,Motion.scalar])]; exact rp_scale _ uζ (hi i)
    rw [show Port.scaleQ i ∘ y = (Port.scaleQ i ∘ g) ∘ pull c' 0 from (by funext x; simp [dance,hl,y,Motion.scalar])]; exact hi i
-- h stuff.
end YM.LocalLTE.River
