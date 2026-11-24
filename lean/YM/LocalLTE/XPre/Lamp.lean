import YM.LocalLTE.River.Wheel
import YM.LocalLTE.XPane.Ink
import YM.LocalLTE.River.Solo
import YM.MergeProof.Ballad
set_option quotPrecheck false
/-!
# Transport in real B-tags including share across sibling sources
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ K ν t v u q:ℝ} {A:Activities G f} {d p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations
-- some type univ physics.
local notation "X"=> Config G f
local notation "F"=> (YM.Labels.frames G).level d
local notation "D"=> localSection G d
-- `d m` ordered for calibration & artwork.
structure Lamp (R: Rep G f) (d:ℕ)(κ:ℝ)(p l:ℕ)(M:Leaf R)(g:X→ ℝ):Prop where
    reads:M.ingredient= RG.masked R.p.threshold M.crest g
    spike : ∃ i:ℕ,M.turn=.logKey i ∧ let q:=(R.activities.reg i).site; M.crest ⊆ neighbors l q ∧ R.p.supBounds q M.crest g M.weight ∧ R.p.Regular M.crest g ∧∃ (B:Config G f→ℝ)(j:Bool)(x:((Labels.frames G).level d).Coeff), g=B+Port.scaleQ j ∘ (Push.Local.presented (localSection G d) q R.p.threshold x)∧ ((Labels.frames G).level d).coeffSize x≤ M.weight ∧ R.p.Regular M.crest B ∧ R.p.supBounds q M.crest B M.weight ∧∃ i≤l,FrameBox.Polynomial i κ q p B
variable {g: Config G f→ℝ}{M: Leaf R}
lemma powered (h:Lamp R d κ p l M g)(hp:d ≤p): Fan.SoloInk M g κ p l ∧ ∀ i,M.turn=.logKey i →(R.activities.reg i).support⊆ neighbors l (R.activities.reg i).site:=by
    obtain ⟨i,hi,ht,hv,hQ,B,j,x,hp',hX,hY,hZ,hV⟩:= h.spike
    refine ⟨⟨⟨_,hi⟩,h.reads,i,hi,hv,hQ,d,hp,x,B,j,hX,hp',hZ,hV⟩,fun i' hh'=>?_⟩
    obtain rfl:i=i':= Wing.logKey.inj (hi.symm.trans hh'); have hx:M.crest=(R.activities.reg i).support:=by unfold Leaf.crest;rw [hi]; rfl
    exact hx ▸ ht
noncomputable def prized (t:ℝ) (ht: 1 ≤ t) (M: Lotus.Leaf R) : Lotus.Leaf R := {M with weight:=t*M.weight,
                                                                                        earn:=fun i=> (M.earn i).trans (le_mul_of_one_le_left M.profit ht) }
section
-- ℝ ports transfer via ℂ. no contraction.Gain price included.
local notation "Z"=> River.rotationP F R.p.order R.p.power
local notation "aM"=> R.p
variable (m': Motion) (a:Site f)(T:R.activities.Moves m'.1 a)
local notation "S'"=> m'.1
local notation "P!"=> XPre.prized (Z) (River.rotation_one _ _) (Leaf.route T M)
variable (d) (H:Lamp R d κ p l M g)(hr:ConnectedActivityE6.Reliable G κ v)

-- Pull material prices. 
variable {L:Support f}{k: Config G f→ℝ}{e:ℝ}

lemma sea (h:R.p.supBounds o L k e)(hp:R.p.Regular L k): R.p.supBounds (turnSites m'.1 a o) (L.image (turnSites m'.1 a)) (k ∘ pull m'.1 a) (rotationP F R.p.order R.p.power *e)∧ R.p.Regular (L.image (turnSites m'.1 a)) (k ∘ pull m'.1 a):=by
   have hB:= Blush.pricingG hp h; have he:= Blush.ornate hp
   have hK:= Push.Local.bound_pull he hB m'.1 a; have hh:= (Port.framesV (Push.Local.regular_pull he m'.1 a) hK false)
   let g':= Complex.ofReal ∘ k; have hv : Port.scaleQ false ∘ (g' ∘ pull m'.1 a)= k ∘ pull m'.1 a:=funext fun i=> rfl
   rw [← hv]; exact ⟨AnalyticBridge.VerifiedReset.sup_le (G:=G) hh.2 (mul_le_mul_of_nonneg_right (rotation_price («F»:=F) R.p.order R.p.power|>.1) h.1), hh.1⟩ -- eta.Local
-- without scalar conj. just real weights. fee. little
lemma global_primary_transport (i:Site f)(z:(F).Coeff) : let Q:= F; let y:=Motion.patch Q (m'.1,false) z
    presented D i R.p.threshold z ∘ pull m'.1 a=presented D (affine m'.1 a i) R.p.threshold y :=by
    intro F' Y; have h : F'= F:=rfl
    funext U; change (D).places ((F).scaled (R.p.threshold)⁻¹ z) _ _= (D).places ((F).scaled (R.p.threshold)⁻¹ Y) (affine m'.1 a i) _
    rw [(D).placed_signed (sound G d),← (F).scaling]; exact rfl
set_option quotPrecheck false
-- need Λ integration.Subscript
include H hr
set_option maxRecDepth 4000 in
lemma carrying : Lamp R d κ p l (prized (rotationP F R.p.order R.p.power) (River.rotation_one _ _) (Leaf.route T M)) (g∘pull m'.1 a):=by
    let P:= XPre.prized (Z) (River.rotation_one _ _) (Leaf.route T M); have he:= MergeProof.crestSky m' a T M
    have hP : P.crest=M.crest.image (turnSites m'.1 a):= he.trans (by rw [shading]); have hx:P.turn=Wing.labelRoute T M.turn:=rfl
    have hs:P.weight=Z*M.weight :=rfl; have hW(i:X): P.ingredient i=M.ingredient (pull m'.1 a i):=rfl
    refine ⟨?_,?_⟩
    · change P.ingredient= _; rw [hP] -- uses occurrences P? wording
      funext i; rw [hW,H.reads]
      by_cases hv: Healthy R.p.threshold (M.crest.image (turnSites m'.1 a)) i; · rw [masked_eq _ _ _ _ hv,masked_eq _ _ _ _ ((healthy_pull ..).1 hv)];rfl
      rw [masked_ne _ _ _ _ hv,masked_ne _ _ _ _ fun h=> hv ((healthy_pull ..).2 h)]
    obtain ⟨i,hi,hX,hV,hL,B,j,x,hv',hp,hR,hb,hQ⟩:=H.spike
    change ∃ i:ℕ,P.turn= _ ∧ _
    let u:= T.ep i -- motion argument likely Moves.rotate reg info
    let o:= (R.activities.reg i).site; let y:= turnSites m'.1 a o; have ho: (R.activities.reg u).site= y:=T.reg_site _
    refine ⟨u,?_,?_⟩; · rw [hx,hi]; rfl
    dsimp only; rw [ho,hP,hs]; obtain ⟨j',hℓ,AX,hX'⟩:= hQ; obtain ⟨hs',heX⟩:= sea (R:=R) d m' a hb hR; obtain ⟨ht',hδ⟩:= sea (R:=R) d m' a hV hL
    let Zx:= (Motion.patch F (m'.1,false) x)
    have hz : ((neighbors l o).image (turnSites m'.1 a))=neighbors l y:=  Scarf.normRange (s:=⟨m'.1,a⟩) (o:=o) rfl _
    have he : g∘ pull m'.1 a=(B∘pull m'.1 a)+ Port.scaleQ j ∘ presented D y R.p.threshold Zx:=by have hx: presented D y R.p.threshold Zx=presented D (R.activities.reg i).site R.p.threshold x ∘ pull m'.1 a:=(global_primary_transport (R:=R) d m' a o x).symm; rw [hv',hx]; exact rfl
    have hp:((Labels.frames G).level d).coeffSize Zx ≤ _ := (patch_cost F _ _).trans (mul_le_mul (rotation_price («F»:=F) R.p.order R.p.power|>.2) hp (Work.G08.size_nonneg ..) (zero_le_one.trans (River.rotation_one ..)))
    let A':FrameBox.Grove y:=FrameBox.Hall.transplanted m'.1 a AX
    refine ⟨(Finset.image_subset_image hX).trans hz.le,ht',hδ, B∘pull m'.1 a,j,Zx,he,hp,heX,hs',j',hℓ,A', ?_⟩
    exact AnalyticBridge.VerifiedReset.Collection.Price.translatedPoly (s:=⟨m'.1,a⟩) AX j' rfl hr (hX')
end
end YM.LocalLTE.XPre
