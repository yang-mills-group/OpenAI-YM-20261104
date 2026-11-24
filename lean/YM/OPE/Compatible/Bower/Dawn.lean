import YM.OPE.Compatible.Bower.Rain
/-!
# First fold at highest date, choosing the port for signed witness.
Receipt up to the moment of use. Prepulses may require much longer
budgets for other slots; retain them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave
open scoped Topology BigOperators Classical
variable {X V I G' T W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p n N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
variable (h:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (S:Wave m U K n)(x:brim D K)(hx: x.val ∈U)
local notation "A!"=> places X+Fintype.card W
local notation "r"=>fun (F:Finset X)=> o∘columns D W F x.val
local notation "r'"=>fun (F:Finset X)=> o'∘columns D W F x.val
local notation "kX"=> fun F=>brimEnd D W F (finishAt D m) k
local notation "sX"=> update (brimEnd D W K (finishAt D m) k) (Sum.inl x) n
local notation "jX"=> update (brimEnd D W K j k) (Sum.inl x) n
local notation "u"=> riseUp W D S
local notation "F'"=>shades' D U x.val a W
set_option quotPrecheck false
-- authorization even before branch origins align. pass for d.
include h hx S
omit [Fintype V][DecidableEq V][Fintype T][DecidableEq T][Fintype G'] in
lemma xMain (hk:k ≤ n)(he:n<N):
    Bind C P E (riseUp W D S) (r U) (r K) n (kX U) sX jX:=by
    have heq:∀ i,k ≤ i → i ≤ n→∀ y:V,y≠P.v→ o x.val i y=affine (P.move y).1 (E i y) (o x.val i P.v):=by
       intro i hi hv y hy
       let v:=x.val; have hr:i ≤ N:= le_trans hv he.le; have hX:v∈allUp D U:= Finset.mem_union_left _ hx
       have hf:= h.honors x.val i hX hi hr; conv => lhs; rw [← hf]; dsimp only [Function.comp_apply]
       rw [h.pays x.val i hX hi hr _ (by rw [← h.fly.start]; exact f.injective.ne hy),show P'.move (f y)= _ from congr_fun h.fly.acts y,show E' i (f y)=E i y from congr_fun (h.turns _ hi hr) y,← h.fly.start,show o' x.val i (f P.v)=o x.val i P.v from congr_fun hf P.v]
    have he' (v:brim D U):roof U m N v.val=N:= if_neg ((on_brim ..).mp v.2|>.1)
    exact Binding.focused (Wave.aim_pledge D W S P E o h.bed (Finset.Subset.refl _) (fun i=> he.le.trans (he' i).ge) (finishAt D m) hk (fun i=>⟨coming D S i,le_rfl⟩) heq (fun _ _=>rfl) (fun _ _=>rfl)) (Sum.inl x) ((solos W D S x).not.mpr (not_not_intro hx))
-- birth & certified act
variable (Y:T×(brim D U⊕W)→ Config G (C.side N p)→ℂ)
local notation "Y₀"=> birth (Names T (↥(brim D U)⊕W)) (C.path.rep N p N) Y
variable (k':ℕ)
-- relay
lemma depart {L:Lights A P N p (brimEnd D W U (finishAt D m) k) N b E (o ∘ columns D W U x.val)} (hN:n < N)(hk:k ≤ n)(hh:C.ref 0 < n)(hW:1 ≤ l n)(ht:∀ i,k ≤ i→Fintype.card G'*(places X+Fintype.card W) ≤ A.r i)(hA:C.Makes)(hG:G.Simple)
   {X₀}(hs: Session P' f L (birth (ManyCopies.Names T _) (C.path.rep N p N) Y) X₀ (shades' D U x.val a W) E' (o' ∘ columns D W U x.val)) :
    let F : T × (brim D K⊕ W)→ Config G (C.side N p)→ℂ :=fun i U' => ∏ j∈(raised W D S).contents i.2, Y (i.1,j) U'
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) F) (prior G _)∧ ∃ S': Lights A P N p sX n b E (r K), ∃ X', Session P' f S' (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) F) n hN.le) X' (shades' D K x.val a W) E' (r' K) ∧
       ∃ hf:∀ i,kX U i≤ n+1, Issues (L.lowers hf hN) (l n) (places X+Fintype.card W) u S' jX :=by
    intro y
    let L₀:=riseUp W D S; let Z:= shades' D U x.val a W; have hp:= S.upper
    have hx':x.val∈allUp D U:= Finset.mem_union_left _ hx
    have he:= xMain D (W:=W) h S x hx hk hN
    have hD(i): kX U i≤ n+1:= (he.fell i).trans n.le_succ
    have hJ:=lives D W h x hx' (Finset.Subset.refl _)
    obtain ⟨X,hX⟩:= Session.cruise hs hA le_rfl hN hD (hh.le.trans n.le_succ) (hJ.sub (hk.trans n.le_succ) le_rfl) (sturdy D W h hx hp hk) (fun i hv he=>
        let ht' : k ≤ i:= (hk.trans n.le_succ).trans hv
        ⟨begun D W h (Finset.Subset.refl _) hx' (ht'.trans i.le_succ) he (ht _ ht'),begun D W h (Finset.Subset.refl _) hx' ht' he.le (ht _ ht')⟩) (shade_well D U _ _ W P')
    obtain ⟨T,X',hF,hS⟩:= Session.dock hX hG hA hN hh ((lives D W h x hx' (Finset.Subset.refl _)).sub hk hN) ((lives D W h x hx' S.next).sub hk hN.le) he (extendable D W h S (Finset.Subset.refl _) hx' hN hk (ht _ hk) hW) (shading D _ _ W S x.2)
    rw [← gust_step C.path N _ _ _ hN] at hF
    obtain ⟨hb,hV⟩:= reuni_gust (riseUp W D S) (raised W D S) (fun _=>rfl) hs.live hN.le; rw [hV] at hF
    exact ⟨hb,T,X',hF,hD,hS⟩
end YM.OPE.Arboreal.Arcade
