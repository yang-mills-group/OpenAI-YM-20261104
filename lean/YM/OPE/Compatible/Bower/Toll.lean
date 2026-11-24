import YM.OPE.Compatible.Bower.Shift
/-! Second wave Bind for pivot + shutter preserves exact survivor. -/
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
    (S:Wave m U K (k+1))(S':Wave m K F k) (x:brim D K)(hx: x.val∈U) (hX:x.val∈ brim D F)
set_option quotPrecheck false
local notation "A!"=> places X+Fintype.card W
local notation "jX"=> brimEnd D W F j k
def inlet (F: Finset X)(x:X)(m:X→ℕ)(k:ℕ) : brim D F ⊕ W→ℕ:= brimEnd D W F (update (finishAt D m) x k) k
omit [Fintype W] in
lemma inlet_port (F:Finset X)(v:brim D F)(k:ℕ) : inlet (W:=W) D F v.val m k= update (brimEnd D W F (finishAt D m) k) (.inl v) k:=by
    funext i; cases i
    next i=> by_cases he:i=v
             · rw [he,update_self]; exact update_self v.val k (finishAt D m)
             rw [update_of_ne (show Sum.inl (β:=W) i ≠ Sum.inl v from fun h=>he (Sum.inl.inj h))]
             exact update_of_ne (Subtype.val_injective.ne he) ..
    next i=> rw [update_of_ne (show Sum.inr i ≠ Sum.inl v from by simp)]; rfl
local notation "sX"=> inlet (W:=W) D F x.val m k
local notation "tX"=> inlet (W:=W) D K x.val m k
local notation "g"=> o ∘ columns D W K x.val
local notation "g'"=> o ∘ columns D W F x.val
local notation "G!"=> o'∘ columns D W K x.val
local notation "P!"=> o'∘ columns D W F x.val
local notation "Z"=> shades' D K x.val a W
local notation "Z'"=> shades' D F x.val a W
include h S S' hx hX
omit [Fintype V][DecidableEq V][Fintype T][DecidableEq T][Fintype G'] in
lemma held (hk:k+1≤ N): Bind C P E (riseUp W D S') g g' k tX sX jX :=by
   let B:= brim D U; let Q:= update (finishAt D m) x.val k; have hx':x.val∈allUp D U:=mem_union_left _ hx; have he: ∀ i:brim D K,k+1 ≤ roof U m N i.val:= S.upward D (Finset.Subset.refl _) N (fun i=> (hk.trans (if_neg ((on_brim ..).mp i.2|>.1)|>.symm.le))) -- args
   refine Wave.aim_pledge D W S' P E o h.bed S.next (fun i=> (Nat.le_succ _).trans (he i)) Q le_rfl ?_ ?_ ?_ ?_
   · intro i; have hf:= coming D S' i; by_cases hv:i.val=x.val
     · obtain rfl:i=x:= Subtype.ext hv; unfold Q; rw [update_self]; exact ⟨le_rfl,hf⟩ -- dependent update type maybe 
     unfold Q; rw [update_of_ne hv]; exact ⟨hf,le_rfl⟩
   · intro i hi hp y hy; have hi':i ≤ N:= hp.trans ((Nat.le_succ _).trans hk); have hf:= h.honors x.val i hx' hi hi'; conv => lhs; rw [← hf]; dsimp only [Function.comp_apply]
     rw [h.pays x.val i hx' hi hi' _ (by rw [← h.fly.start]; exact f.injective.ne hy),show P'.move (f y)= _ from congr_fun h.fly.acts y,show E' i (f y)=E i y from congr_fun (h.turns _ hi hi') y,← h.fly.start,show o' x.val i (f P.v)=o x.val i P.v from congr_fun hf P.v]
   · intro i hi; refine update_of_ne (show i.val≠x.val from ?_) ..; intro hq; exact ((on_brim ..).mp x.2).1 (hq ▸ hi)
   intro i hi; refine update_of_ne ?_ ..; intro hh; obtain rfl:i=x:= Subtype.ext hh
   let z:brim D F:=⟨i.val,hX⟩; have h: topHat D S' i=z:= (topper D S' _ z).2 le_rfl; rw [h] at hi; exact ((on_brim ..).mp i.2).1 hi
lemma rolled (hA:C.Makes)(hG:G.Simple)(hN:k+1 ≤ N)(hp:C.ref 0 < k)(hW:1 ≤ l k)(hc:Fintype.card G'*(places X+Fintype.card W) ≤ A.r k)
    {F': T×(brim D K⊕ W)→ Config G (C.side N p)→ℂ}{Y : Lights A P N p tX (k+1) b E g}{X₀}
    (hv:Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) F') (prior G _))
    (hh: Session P' f Y (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) F') (k+1) hN) X₀ Z E' G!):
    let y' : T×(brim D F ⊕ W)→ Config G (C.side N p)→ℂ:= fun i U' => ∏ j∈(raised W D S').contents i.2,F' (i.1,j) U'
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) y') (prior G _) ∧ ∃ T': Lights A P N p sX k b E g', ∃ X', Session P' f T' (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) y') k ((Nat.le_succ _).trans hN)) X' Z' E' P! ∧ Issues Y (l k) (places X+Fintype.card W) (riseUp W D S') T' jX:=by
    intro q; have hx':x.val∈allUp D U:=mem_union_left _ hx
    obtain ⟨V,x',he,hi⟩:= Session.dock hh hG hA hN hp ((lives D W h x hx' S.next).sub le_rfl hN) ((lives D W h x hx' (S'.next.trans S.next)).sub le_rfl (le_trans k.le_succ hN)) (held D h S S' x hx hX hN) (extendable D W h S' S.next hx' hN le_rfl hc hW) (shading D _ _ W S' hX)
    obtain ⟨ht,hK⟩:= reuni_gust (A:=C.path) (riseUp W D S') (raised W D S') (fun _=> rfl) hv (le_trans k.le_succ hN); rw [← gust_step C.path N _ _ _ hN,hK] at he; exact ⟨ht,_,_,he,hi⟩
end YM.OPE.Arboreal.Arcade
