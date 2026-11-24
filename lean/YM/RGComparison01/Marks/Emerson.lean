import YM.RGComparison01.Marks.Hoboken
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Hoboken
open Lanes Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
variable {X : Metals G} {Δ: Rolls X.p} {A : Alloy X Δ} (F: Roost.Factor A)
variable {m N k Y b n w D:ℕ} {C F' :Side} {β : ℝ}{σ:Type}
    (h : f.val=c.val*(A.B.a.S.block m).val) (H : F'.val=C.val*(A.B.a.S.block m).val)
    (l:4*Y+16 ≤ c.val)
    (R:RG.Rep G f)(R₁:RG.Rep G F') (M:σ→ Lotus.Leaf R)(M₁:σ→Lotus.Leaf R₁)(g:σ→ℝ)
    (J : Boulevard.Chartlet F.shape A N m h R) (J₁:Boulevard.Chartlet F.shape A N m H R₁)
local notation "Y'"=> A.B.a
local notation "x₀"=> A.B.a.clock.hatBeta m
local notation "t₀"=> (A.B.a.budget m)
local notation "B"=> radiusB x₀
local notation "Z₁"=> (A.B.a.S.block m)
local notation "O"=> Chi.canonical
set_option quotPrecheck false
local notation "Pk"=> (A.B.a.clock.op m 0).patch
variable (E:Ribbon R b)(E₁:Ribbon R₁ b)
set_option quotPrecheck false
variable (l':4*Y+16 ≤ C.val)
local notation "C''"=> (Library.deck c C)
local notation "F''"=> (C'') * ((A.B.a.S.block m))
local notation "hq"=> (show (C'').val = c.val*C.val from rfl)
local notation "hq'"=> (show (C'').val = C.val*c.val from mul_comm ..)
open Stowe
section pair
variable (x:Site (Library.deck c C))(R': RG.Rep G ((Library.deck c C)*(A.B.a.S.block m))) (Z':Ribbon R' b) (Q':σ→Lotus.Leaf R') (z:σ)
-- Entire Ghost necessary for period but no claims it obeys model height values
lemma mustW (C Y:ℕ) (l:4*Y+16 ≤ C): 2 ≤ C:=by omega
lemma wcap (C Y:ℕ) (l:4*Y+16 ≤ C): 2*(2*Y) ≤ C:=by omega
structure Holo (N:ℕ)(β:ℝ) (Y:ℕ)(hL :4*Y+16 ≤ c.val)(hL':4*Y+16≤C.val) : Prop where
   views : Library.Visible A m N (c:=Library.deck c C) rfl R' β
   actualLeg : ∃ (t:Z'.Node→E.Node)(u:σ→Z'.Node), Relay.Lens (h:=h) (H:=show ((Library.deck c C)*(A.B.a.S.block m)).val= _ from (show _=(Library.deck c C).val*(A.B.a.S.block m).val from rfl)) (hC:=hq)
      (P:=(A.B.a.clock.op m 0).patch) (he:=mustW _ _ hL) M Q' E Z' t u x Y
   pen : ∃ (t:Z'.Node→E₁.Node)(u:σ→Z'.Node), Relay.Lens (h:=H) (H:=show ((Library.deck c C)*(A.B.a.S.block m)).val= _ from (show _=(Library.deck c C).val*(A.B.a.S.block m).val from rfl)) (hC:=hq')
      (P:=(A.B.a.clock.op m 0).patch) (he:=mustW _ _ hL') M₁ Q' E₁ Z' t u x Y
   anchor : x ∈ (Q' z).crest.image (decreed (P:=(A.B.a.clock.op m 0).patch) (c:=Library.deck c C) rfl).parent
local notation "Z"=>splitter (Deck.divides hq)
local notation "Zt"=>splitter (Deck.divides hq')
local notation "V'"=> normal (Deck.divides hq) hq
local notation "Vt"=> normal (Deck.divides hq') hq'
variable [Fintype σ]
variable (h₁: Library.Visible A m N h R β)(h₂:Library.Visible A m N H R₁ β)
    (h₃: Holo h H R R₁ M M₁ E E₁ x R' Z' Q' z N β Y l l')
    (hK: std F m b ℓ ≤ Y)
variable (p:Finset σ) (hp:z∈p) (J' : Chartlet F.shape A N m (show (Library.deck c C * (A.B.a.S.block m)).val=(Library.deck c C).val*((A.B.a.S.block m)).val from rfl) R') (hJ : Shed J' Q' g (A.B.a.budget m) Chi.canonical)
local notation "A₀"=> Drawing.cabinet J E
local notation "A₁"=> Drawing.cabinet J₁ E₁
local notation "G₀"=> Drawing.cabinet J' Z'
local notation "Xs"=> Cabinet.garage (Library.spread F m b) ℓ
include h₁ h₂ h₃ hK hp hJ
set_option maxHeartbeats 600000 in
lemma visits (V:Config G c)(V₁:Config G C)(hV:RG.flags (A.B.a.budget m).threshold V=∅)(hZ:RG.flags (A.B.a.budget m).threshold V₁=∅)
    (hA:Agrees (Lattice.box Y) (expandAt (Z x) V) (expandAt (Zt x) V₁)) (hr:1 ≤ ℓ) : Z x ∈ (M z).crest.image (Pane.panel A m h).ratio.parent ∧ Stowe.ship M g J A₀ ℓ k p V (χ:=O)= Stowe.ship M₁ g J₁ A₁ ℓ k p V₁ (χ:=O):= by
  obtain ⟨α,θ,hT⟩:= h₃.actualLeg; obtain ⟨α',θ',hT'⟩:= h₃.pen
  obtain ⟨hm,hF⟩:= midnight F h rfl (hq) l _ _ M _ g J J' E Z' x p z hp h₃.anchor hK hr h₁ h₃.views hT V hV (k:=k)
  obtain ⟨hy,hP⟩:= midnight F H rfl (hq') l' _ _ M₁ _ g J₁ J' E₁ Z' x p z hp h₃.anchor hK hr h₂ h₃.views hT' V₁ hZ (k:=k)
  have hC: 4*Y+16≤ (C'').val:= l.trans (Nat.le_mul_of_pos_right _ C.pos); let W₀:= (V').links V; let W₁:= (Vt).links V₁
  have hc: Agrees (neighbors Y x) W₀ W₁:= by
    apply Slide.readNear x (by omega); unfold W₀ W₁; rw [Slide.rolls,Slide.rolls]; exact hA
  let f':= Stowe.tale Q' g J' G₀ ℓ k p (χ:=O); have hg : (t₀).Regular (neighbors Xs x) f':= Stowe.stay _ _ _ _ _ hJ.canopy _ _ _ hp h₃.anchor
  have he: W₀= (V').links V:=rfl
  have hz:RG.flags (A.B.a.budget m).threshold W₀=∅:= by ext i; rw [show i∈flags _ _ ↔ _ from Deck.flagged hq V i (by omega) (t₀).threshold,hV]; simp
  have hz':RG.flags (t₀).threshold W₁=∅:= by ext i; rw [show i∈flags _ _ ↔ _ from Deck.flagged hq' V₁ i (by omega) (t₀).threshold,hZ]; simp
  refine ⟨hm,hF.symm.trans ((Lanes.garden J' Q' g Z' (t₀) hJ W₀ p hz).trans ((hg.sites _ _ ?_).trans ((Lanes.garden J' Q' g Z' t₀ hJ W₁ p hz').symm.trans hP)))⟩
  exact agrees_mono hc (fun i hi=>(neighbors_mem ..).mpr (((neighbors_mem ..).mp hi).trans hK))

-- Stitched real.Health on both ROOT anchors. Normalize.P.MOV.
local notation "X0"=> Z x
local notation "X1"=> Zt x
variable (hr:1≤ℓ)(hk:3*Y≤n)(V:Config G c)(hv: Healthy (A.B.a.budget m).threshold (neighbors n (splitter (Deck.divides (show (Library.deck c C).val=c.val*C.val from rfl)) x)) V)
    (hw:Shed J M g (A.B.a.budget m) Chi.canonical) (hW:Shed J₁ M₁ g (A.B.a.budget m) Chi.canonical)
include hW hw hr hv hk
set_option maxHeartbeats 500000 in
lemma valley : Stowe.tale M g J A₀ ℓ k p V (χ:=O)= Stowe.tale M₁ g J₁ A₁ ℓ k p (Rotunda.bake (M:=Y) (G:=G) (f:=C) (Z x) (Zt x) (wcap _ _ l') V) (χ:=O):= by
   let K:=(t₀); let y:= Z x; let B':= Rotunda.bake y (Zt x) (wcap _ _ l') V
   obtain ⟨U,hU,hA⟩:= Slide.shifts V y Y (by omega) K.threshold K.threshold_pos.le (hv.mono_left (show neighbors Y y⊆ neighbors n y from (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))))
   have hX: flags (K).threshold B'=∅:= Rotunda.staffed _ _ _ _ _ hk hv -- args count
   have ht: Agrees (Lattice.box Y) (expandAt y U) (expandAt (Zt x) B') := fun i hi hj=> (hA i hi hj).trans ((Rotunda.aim _ _ V («f»:=C) (M:=Y) _ i hi hj).symm)
   obtain ⟨hx,hz⟩:= visits F h H l R R₁ M M₁ g J J₁ E E₁ l' x R' Z' Q' z h₁ h₂ h₃ hK p hp J' hJ U B' hU hX ht hr (k:=k)
   have he := (Stowe.stay M g J (Drawing.cabinet J E) K hw.canopy _ _ _ hp hx (ℓ:=ℓ) (k:=k)).sites U V (agrees_mono (Slide.readNear _ (by omega) hA) (fun i hi=>(neighbors_mem ..).mpr (((neighbors_mem ..).mp hi).trans hK)))
   exact he.symm.trans ((Lanes.garden J M g E K hw U p hU).symm.trans (hz.trans (Lanes.garden J₁ M₁ g E₁ K hW B' p hX)))
end pair
end Hoboken
end YM.RGComparison01.Pledge
