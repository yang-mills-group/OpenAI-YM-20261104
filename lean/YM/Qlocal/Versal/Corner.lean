import YM.Qlocal.Versal.Brandi
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c f C F: Side} {W₀:Burn.Locale G} {R:RG.Rep G f} {R':RG.Rep G F}
    {p p' : ℝ} {n b ℓ r k:ℕ}
-- ℓ capacity, one labelled copy per site, for either analytic ζ or further spends.
variable {X:Burn.Seed R W₀}
namespace Pad
variable (Z:Pad X k)
open PhysicalNext.Repeat.Lotus Merge.Palette Ovens
section
variable {B:Patch}{c1 F1:Side} {h : f.val=c.val*B.L.val} {H : F.val = C.val*B.L.val} {hC:C.val=c.val*ℓ} {he:2 ≤ c.val} 
variable {ι:Type}(x:ι→Names f k) (x':ι→Names F k) (Q:ι→ Config G f→ℝ) (Q':ι→ Config G F→ℝ) {w1 w2:ι→ℝ}
    (S:∀ i,Herb R.p (x i|>.1) (Q i) (w1 i)) (S':∀ i,Herb R'.p (x' i|>.1) (Q' i) (w2 i)) {X':Burn.Seed R' W₀} (Z':Pad X' k)
local notation "T"=> fun i=>bark Z (Q i) (S i)
local notation "T'"=> fun i=>bark Z' (Q' i) (S' i)
variable (hb:R.p.B≤b) (hb':R'.p.B≤ b) (hr:R'.p=R.p)
set_option quotPrecheck false
local notation "L"=> (Lace.project (H:=H) (h:=h) hC he)
local notation "Y"=> lower Z hb Z' hb' (Deck.fineP h H hC)
variable (hQ:∀ i,Q i=Q' i ∘ (Lace.project (H:=H) (h:=h) hC he).high.links) -- sufficient, can actually need only Healthy. 
variable (hf:∀ i, (x i).1=(Lace.project (H:=H) (h:=h) hC he).high.cut (x' i).1) (hS:∀ i,(x i).2=(x' i).2)
    (o: Site C) (hm:∀ i,separation o ((decreed H).parent (x' i).1)≤n)
-- Transport per entry; includes all.B.Entity.Out.Funding. Use to assemble angular payout. 
local notation "f'"=> Z'.thread hb'
local notation "f!"=> Z.thread hb
include hf hS hm hr hQ
lemma lens (ht:4<f.val): Relay.Lens (h:=h) (H:=H) (hC:=hC) (he:=he) (T) (T') (Z.thread hb) (Z'.thread hb') (lower Z hb Z' hb' (Deck.fineP h H hC)) (fun i=> Z'.node hb' (.inr (x' i))) o n:= by
 have hv i: sends (Deck.fineP h H hC) (Sum.inr (x' i))=Sum.inr (x i) := congr_arg Sum.inr (Prod.ext (hf i).symm (hS i).symm)
 refine ⟨roll Z hb Z' hb' (Deck.fineP h H hC) hr ht, fun i=> rfl, fun i => ?_, fun i=>?_, fun i U=> ?_⟩
 · unfold lower; rw [Equiv.symm_apply_apply,hv]; rfl
 · rw [tag]; exact hm _
 let K:= R.p; let y:= (x i|>.1); let v:=(x' i|>.1); let V:= (L).high.links U; change masked R.p.threshold (court (x i).1 R.p.B) (Q i) U = masked R'.p.threshold (court (x' i).1 R'.p.B) (Q' i) V; have hF: court y K.B=(court v K.B).image (L).high.cut:= by unfold y; rw [hf]; unfold court; rw [← Finset.image_singleton]; exact Deck.ringed (Deck.fineP h H hC) ..
 have hp:Healthy R.p.threshold (court (x i).1 R.p.B) U ↔ Healthy R.p.threshold (court (x' i).1 R.p.B) V := by change Healthy _ (court y K.B) _ ↔ _; rw [hF]; exact (Deck.vigor (Deck.fineP h H hC) U ht ..).symm
 rw [hr,hQ i]; by_cases hx: Healthy R.p.threshold (court y R.p.B) U; rw [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ (hp.mp hx)]; rfl; rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ (mt hp.mpr hx)]
-- auxiliary agreement analytic gauge proofs later.Arr.
end
-- E budget outside ribbon.Hands. normal and ghost.C.Valid. doesn't require Candor.town invariant here. Good for renamed slots. 
variable (h:R.p.B≤ n)
local notation "I"=> Pad.thread Z h
local notation "A"=> R.activities
lemma opens0 (hx:Pad.faded X): Drawing.Opens (thread Z h) (fun _=>False):= by
 refine ⟨fun _ ht=> ht.elim,fun i hi hp U=>?_⟩; have he0 : i∉ Set.range X.model:= by rintro ⟨j,hj⟩; exact hp ⟨.inl j,hj⟩
 simp only [Activities.regularOccurrence,hx i he0]; unfold masked Set.indicator; split<;> rfl
lemma charges (ht:Candor R.p R.activities (Set.range X.model) p p') : (Tithe.portion R.activities (fun i=>¬(thread Z h).keep i)).EBound R.p p' := by
 let f:=fun i=> ¬(thread Z h).keep i; obtain ⟨⟨v,hv,H⟩,-⟩:= ht; let v' (i:ℕ):= if f i then v i else 0; let T' := (A); let U:= Tithe.portion T' f; refine ⟨v', fun i=>?_, fun x=>?_⟩
 · change R.p.supBounds _ _ ((Tithe.portion R.activities f).E i) _; by_cases H:f i
   · unfold Tithe.portion v'; simp_rw [if_pos H]; exact hv _
   unfold Tithe.portion v'; simp_rw [if_neg H]; simpa only [abs_zero] using! (AnalyticBridge.CouplingShape.sup_const (G:=G) (p:=R.p) (o:=((A).reg i).site) (X:=((A).reg i).support) (0:ℝ))
 apply budget_mono ((H x).2)
 · intro i; split
   · apply mul_nonneg (Real.exp_nonneg _); unfold v'; split; exact (hv i).1; rfl
   rfl
 intro i; have h1 (i) := ((H x).2).1 i; split; swap; · exact h1 i
 rename_i heq; by_cases h0:f i; swap; · unfold v'; rw [if_neg h0]; unfold BudgetPoint.mass; rw [mul_zero]; exact h1 i
 have h2:i∉ Set.range X.model:= by rintro ⟨d,rfl⟩; exact h0 ⟨.inl d,rfl⟩
 unfold v'; rw [if_pos h0,if_neg h2,Burn.wallet,if_pos (show (R.activities.reg i).site=x from heq)]; rfl
end Pad
end YM.Qlocal.Versal
