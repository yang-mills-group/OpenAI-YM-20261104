import YM.OPE.Compatible.Copper.Metal
/-!
# Restore one pivot through Ore. continuum grade can reproject. Exterior estimates of
first balance obtained from `tunes` (literally v heap grants Remains). Need second balance from observers. Output grade via Lanes.out. No constants depend on choice of replacement reps. This first tier at exact authenticated mesh points.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F:Finset X}
   {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}{T:Spec.Final C Λ S}(A:Allot C) {P:Prescription T.sector.derivatives}
   [Fintype I]
variable {p:X→ C.book.Token} (u:X)(hp:Crown U)(hu:u∈rest U)
variable {y:X→ Cover}{s:I→ C.book.Token} {W J₀ k n N r d e:ℕ}{a:C.label d}{t:C.label e}
set_option quotPrecheck false
local notation "I'"=>brim D U
local notation "J"=>glen D U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "p₀"=>picked I' p
local notation "p₁"=> picked H (update p u (⟨d,a⟩:C.book.Token))
local notation "L"=> T.sector.derivatives
variable {x x' z z':ℝ}
variable (h:TokenMine D C Λ U (picked (brim D U) p) u y W J₀ k n d e a t x x' z z')
local notation "s'"=> picked J (fun i=>y i-y u)
include h
lemma swivelMine : Survival (C:=C) Λ J₀ k W x' x (picked J p) (picked J (fun i=> y i-y u)) d a:=by
   obtain ⟨hx,hQ,f,hf,hL,g,hG,g',hT,hR⟩:= h; refine ⟨hx,⟨f,g,hf,hL,hG,⟨?_⟩,hR.mono fun _ h=>h.pay⟩⟩ -- layout
   filter_upwards [hR] with i hi; have H1:= hi.support; change Cards.PaidAt _ _ _ _ _ _ ((Cards.register C W (picked J (fun i=> y i-y u)) (germ (frozen C (picked J p))) i.1 i.2) - C.O i.1 i.2 (g (i.1,i.2)) 0); rw [← belly_register]; exact H1
lemma token_fees : 0 ≤ x' ∧ 0 ≤ z':= by obtain ⟨hx,hQ,f,hf,hL,g,hG,g',hT,hR⟩:= h; exact ⟨hR.exists.choose_spec.support.cost,hR.exists.choose_spec.edge.cost⟩
omit h
-- uniform cap for a schedule
variable (hΓ: Org.Grill C Λ)
include hΓ
variable (w:I→ C.book.Token){c:ℝ}
local notation "Ω"=> C.S.gridPoint W
-- p' transported
lemma viewed_root (hc:0<c) : ∀ᶠ j:ℕ in atTop,∃ B:ℝ,0 ≤ B∧ ∀ W:ℕ,j ≤ W → ∀ {X:Type}[PartialOrder X][OrderBot X][Fintype X] (D:Origin X)(U:Finset X)(u:X), Crown U→ u∈rest U → ∀ (p p':X→ C.book.Token), (∀ x∈brim D U,S.classTokens (p' x)= S.classTokens (p x)) →∀ (y:X→ Cover), Screen (picked (brim D U) (C.S.gridPoint W ∘ y)) → Screen (picked (brim D (Arboreal.trim U u)) (C.S.gridPoint W ∘ y))→∀ {x x' z z':ℝ} {k n d e:ℕ}{a:C.label d}{t:C.label e}, TokenMine D C Λ U (picked (brim D U) p') u y W j k n d e a t x x' z z' → ∀ (i:I→E4), ClearOf 0 i c → Injective (beside (picked (brim D U) (C.S.gridPoint W ∘ y)) i) → Injective (beside (picked (brim D (Arboreal.trim U u)) (C.S.gridPoint W ∘ y)) i)→ ∀ r:Viewers T,
    ‖(observe (spectator T r) (beside (picked (brim D U) (C.S.gridPoint W ∘ y)) i) (beside (picked (brim D U) p) w)- observe (spectator T r) (beside (picked (brim D (Arboreal.trim U u)) (C.S.gridPoint W ∘ y)) i) (beside (picked (brim D (Arboreal.trim U u)) (update p u (⟨d,a⟩: C.book.Token))) w))- observe (spectator T r) (beside (sole (0:E4)) i) (beside (sole (⟨e,t⟩: C.book.Token)) w)‖≤ z'*B:=by
   filter_upwards [billedThird T hΓ w hc] with j h
   obtain ⟨B,hB,h⟩:=h; refine ⟨B,hB,fun W hW X _ _ _ D U u hp hu p p' hh y hS hS' x x' z z' k n d e a t H' i he hx hx' r=>?_⟩
   obtain ⟨hk,hP,f,hf,hF,g,hG,Q,hQ,h'⟩:=H'
   let o:=brim D U; let F':= Arboreal.trim U u; let l:=brim D F'; let V:=C.S.gridPoint W
   have hM:∀ᶠ y' in f, Cards.PaidAt C.S y'.1 y'.2 j (C.beta y'.1 y'.2) z' ((Cards.register C W (picked o y) (germ (frozen C (picked o p'))) y'.1 y'.2- Cards.register C W (picked l y) (germ (polesAt p' u a g l)) y'.1 y'.2)-C.O y'.1 y'.2 (Q y') 0):=by
       filter_upwards [h'] with i hi; dsimp only [o,l,F']; rw [← edge_register D p' u hp hu]; exact hi.edge
   let c':C.book.Token:= ⟨d,a⟩; let s'':= spectator T r
   have hA(b:Viewers T): (spectator T b).Symmetric := (spectate T b).laws.toSymmetric
   have hv:=h W hW (picked o y) (picked l y) hS hS' hF (fun _=>tendsto_const_nhds) (poles_tend p' u a g l hG) hQ hM i he hx hx' r
   have ht(α : Type)[Fintype α](x:α→E4)(p p':α→ C.book.Token)(he:∀ i,S.classTokens (p' i)=S.classTokens (p i))(hx:Injective (beside x i)): observe s'' (beside x i) (beside p' w)= observe s'' (beside x i) (beside p w) := sees_same _ (hA _) (spectate_respects T r) (fun i=>by cases i; exact he _; rfl) hx
   rw [← ht _ _ (picked l (update p u c')) (picked l (update p' u c')) ?_ hx',← ht _ _ (picked o p) (picked o p') (fun i=>hh _ i.2) hx]; exact hv
   intro i
   rcases (frontier_trim D U hp ((rest_mem _).mp hu|>.1) ((rest_mem _).mp hu|>.2)).mp i.2 with hh'|he'
   · unfold picked; dsimp only [Function.comp_apply]; rw [hh',update_self,update_self]
   unfold picked; dsimp only [Function.comp_apply]; have hr:i.val≠u:=fun h=> he'.2 h.ge; rw [update_of_ne hr, update_of_ne hr]; exact hh _ he'.1
end YM.OPE.Arboreal.Pixel
