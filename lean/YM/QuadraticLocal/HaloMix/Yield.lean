import YM.QuadraticLocal.Travel
import YM.QuadraticLocal.HaloMix.Pound
/-!
# Rooted proportional booking. Don't charge any unmarked cost to K-entry slice.

`Trigger.Payment` is the first seal. We need another Seal, on exactly those
 witnesses, charging ONLY the marked part of K to the relative input force
 budget. For output assemble by sharpening K-Paid, so BOTH even before exponent
 render and vacuum actual coupling reset. Unmarked true invalid terms keep zeros;
 not buying unnecessary supersLOTS. Deboost proves the returned K assertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Throng
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Payments Rack
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n c : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι μ T : Type*} {w w' : V → ℝ} {a α β δ γ κ k m b W D r : ℝ} {B : ℕ}
namespace Hard
open GridRenewal.Rain
-- Ferry.
def active (w:V→ℝ)(x:Poly R):ℝ:= Poly.price w (fresh x)
lemma hotPart (x : Poly R)(i:R.Mode): (fresh x).part i= if i=R.quiet then 0 else x.part i:= by
    split; next h=> subst i; exact unwritten _
    next h=> change _- (Poly.send R.quiet _).part i = _; rw [Poly.part_send,if_neg h,sub_zero]; rfl
lemma wholly (x:Poly R) : Poly.price w x= ‖x.part R.quiet‖+active w x:= by
    simp only [active, Poly.price]; let g:= x.part
    have he i: Poly.toll w i*‖x.part i‖= (if i=R.quiet then ‖x.part R.quiet‖ else 0)+ Poly.toll w i*‖(fresh x).part i‖:=by
         rw [hotPart]; split; next h=> subst i; simp
         next=> simp
    -- prove with add summation simpler
    simp_rw [he]; rw [sum_add_distrib]; simp
lemma helix (x:Poly R)(h:0≤α): active w (boom α x)= α * active w x:=by
    unfold active Poly.price; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [hotPart,hotPart]; split; simp; next H=>
       rw [Throng.paid,weight,if_neg H,norm_mul,Complex.norm_real,Real.norm_of_nonneg h]; ring
variable (hp:1≤α)(hw:∀ i,0<w i)
include hw
lemma active_nonneg (p:Poly R):0≤active w p:=Poly.nonnegative hw _
variable {P:ℕ→ForcedAddress G n}{F:Code G n}(H: QuadraticLocal.Hard T p P F o R)
-- Note: these are full coefficientwise l1-Poly bills, for SUP over independent
-- test args of each operation PRIOR TO per-vertex prices, not Hit on evaluation.
structure Pair (w:V→ℝ)(B:ℕ)(a u v:ℝ): Prop where
  cashout : ∃ f:ℕ→Poly R,(∀ i t U,Width.Covered (H.hard t i U) (f i)) ∧
     Hit (fun i=>(P i).support) B (fun i=> Poly.price w (f i)) a u ∧ Hit (fun i=>(P i).support) B (fun i=>active w (f i)) a v
lemma Pair.used (h:H.Paid w B a m): Pair H w B a m m:=by
   obtain ⟨f,hf,hG⟩:=h.wages; refine ⟨f,hf,hG,fun i=>budget_mono (hG i) (fun j=>by split; exact mul_nonneg (active_nonneg hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>by split; exact mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (wholly _).symm) (Real.exp_pos _).le; exact le_rfl)⟩
omit hw
lemma Pair.mono (h:Pair H w B a m b)(he:m≤W)(ht:b≤r): Pair H w B a W r:=by obtain ⟨f,hf,hM,hB⟩:=h.cashout; exact ⟨f,hf,fun i=>budget_loosen (hM i) he,fun i=>budget_loosen (hB i) ht⟩
include hw hp
lemma Pair.theatre (h:(metal H α).Paid w B a m): Pair H w B a m (α⁻¹*m):= by
   obtain ⟨f,hf,hG⟩:=h.wages; let g i:= boom α⁻¹ (f i); have ha:0<α:=zero_lt_one.trans_le hp; have hb:= inv_pos.mpr ha
   refine ⟨g,fun i t U ν=>?_ ,fun i=>budget_mono (hG i) (fun j=>by split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>?_),fun i=> budget_mono (budget_scale hb.le (hG i)) (fun j=> by split; exact mul_nonneg (active_nonneg hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>?_)⟩
   · let x:= H.hard t i U; let ht:= hf i t U ν; change ‖(boom α x).part ν‖≤_ ∧ _ at ht; change ‖x.part ν‖≤_ ∧ _; by_cases h:ν=R.quiet
     · subst ν; unfold g; rw [silent] at *; exact ht
     unfold g; rw [paid]; rw [paid] at ht; simp only [weight,h,ite_false,norm_mul,Complex.norm_real,Real.norm_of_nonneg ha.le,Complex.mul_re,Complex.mul_im,Complex.ofReal_re, Complex.ofReal_im, ht.2,mul_zero,zero_mul,add_zero,sub_zero] at *; constructor
     · rw [← div_eq_inv_mul]; exact (le_div_iff₀ ha).2 ((mul_comm ..).trans_le ht.1)
     trivial
   · split; next=>
       apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; dsimp only [g]; rw [wholly,silent,helix _ hb.le,wholly (f j)]; exact add_le_add_right (mul_le_of_le_one_left (active_nonneg hw _) (inv_le_one_of_one_le₀ hp)) _ -- order?
     next=>exact le_rfl
   · split; next=>
       rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; dsimp only [g]; rw [helix _ hb.le,wholly]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hb.le
     next=>rw [mul_zero]
end Hard
variable {P:Rep G n}
open Travel
open PhysicalNext PhysicalNext.Repeat Lotus Merge Palette RemainderComparison RemainderComparison.Lyric RemainderComparison.Typeface
open Trigger
variable {I:Type} [Countable I]
variable (A: Gallery T I o P R)(S:StepData c n)(U:Seal A w b m)
structure Ledger (c':ℝ): Prop where
   ark : Hit (fun i=>(P.activities.forced i).support) P.p.B (fun i=> Hard.active w (U.crown i)) P.p.supportExponent c'
variable (h: Ledger A U r)
omit [Countable I] in
lemma certificates (h:A.E.Paid w P.p.B P.p.supportExponent b)(hh:Throng.Hard.Pair A.K w P.p.B P.p.supportExponent m r): ∃ U:Seal A w b m, Ledger A U r:=by
    obtain ⟨e,hp,hF,hZ⟩:= h.budget; obtain ⟨f,hf,hG,hM⟩:= hh.cashout; exact ⟨⟨e,f,hp,fun t i=> hF i t, hf,hZ,hp,hG⟩, ⟨hM⟩⟩
local notation "X"=> P.activities
set_option quotPrecheck false
local notation "Fog'"=> Fog (fun i=>((P.activities).forced i).support) R o
local notation "J"=> Trigger.Table A
local notation "P₀"=> P.p
local notation "sH"=> U.supE
local notation "s₀"=> U.crown
local notation "D'"=> Fintype.card (Site (S.ratio.count))
-- `A.ledger` & U.payment at SAME σ: pay Fuel costs independent of copies over all
-- Θ-augmented.Frame; actor t chosen arbitrarily. Uses all labels on actual mask.
private lemma doubled {ι:Type} (X_:ι→Support n) (f:ι→ℝ) {B a b} (h:Hit X_ B f a b): Hit (fun i:ι×Bool=> X_ i.1) B (fun i=> f i.1) a (2*b):= by
    intro x; let g i:= if x∈ X_ i then f i * Real.exp (a*(coverNumber B (X_ i):ℝ)) else 0
    have hT: SumBudget g b:= h x; have he: SumBudget (fun (_:Bool)=> (1:ℝ)) 2:=budget_finite (fun _=>zero_le_one) (by simp)
    show SumBudget (fun i:ι×Bool=> g i.1) (2*b); simpa only [mul_one,mul_comm b] using! budget_prod hT he

variable (hw:∀ i,0<w i)(H: HasSlots P.p P.activities)
local notation "ξ"=> Trigger.listCosts A w hw H (U.supE) (U.crown) (sighting A w U) U.looks
include hw h
omit [Countable I] in
lemma splitPays : Hit (fun i:Fog' => ((X).forced i.val.1).support) P.p.B (fun i:Fog'=>Poly.toll w i.val.2 * ‖(U.crown i.val.1).part i.val.2‖) P.p.supportExponent r := by
   have hx: Hit (fun i:ℕ×R.Mode=> ((X).forced i.1).support) P.p.B (fun i:ℕ×R.Mode=> Poly.toll w i.2 * ‖(GridRenewal.Rain.fresh (U.crown i.1)).part i.2‖) (P).p.supportExponent r:= CoefficientPrices.tallyI («p»:=P.p) _ _ h.ark (fun i (j:R.Mode)=> Poly.toll w j * ‖(GridRenewal.Rain.fresh (U.crown i)).part j‖) (fun i j=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun i=>le_rfl)
   intro x; apply Eq.mp (?_ : _ = _) (budget_pull (Subtype.val : Fog (fun i=>(P.activities.forced i).support) R o → ℕ×R.Mode) (Subtype.val_injective) (hx x)); congr 1; ext1 i; dsimp only [Function.comp_apply]; rw [Hard.hotPart,if_neg i.property.1]


lemma estimates (t:T): Lyric.Scale id (fun i=>(brand ξ t i).crest) (brand ξ t) (fun _=>1) (Fintype.card (Site (S.ratio.count))) P.p.supportExponent (2*(b+r)) S:=by
    let a:= P.p.supportExponent; let Y (i:J):Support n:= i.elim (fun i=>A.E.ground i.val) (fun i=> ((X).forced i.val.1).support); let f:=cape A w U.supE U.crown
    have hN i:(Y i).Nonempty:=by cases i; exact ⟨_,(A.E.address _).anchor⟩; exact ForcedAddress.inventory_ne ((X).forced _) |>.mono ( (X).forced _|>.inventory_sup)
    have he i:0 ≤ f i:=by cases i; exact mul_nonneg (Poly.worth hw _).le (U.perE _); exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _)
    have hY i : (brand ξ t i).crest=Y i.1:= wingE A H _ _
    have hh(i:J×Bool): Palette.wages (brand ξ t) (fun _=>1) i=f i.1:= one_mul _
    have hH : Hit Y P.p.B f a (b+r):= by
       intro x
       let u i:= if x∈Y i then f i*Real.exp (a*(coverNumber P.p.B (Y i):ℝ)) else 0
       have h₁: SumBudget (u ∘ Sum.inl) b:=budget_pull (Subtype.val : Fires A→ I) (show Injective (Subtype.val («p»:=fun i=> ¬ A.E.clear i)) from Subtype.val_injective) (U.payment.bright x)
       have h₂: SumBudget (u ∘ Sum.inr) r:= splitPays A U h hw x
       have he:= HasSum.sum (f:=u) h₁.2.1.hasSum h₂.2.1.hasSum; refine ⟨fun i=>?_,he.summable,he.tsum_eq.trans_le (add_le_add h₁.2.2 h₂.2.2)⟩; cases i; exact h₁.1 _; exact h₂.1 _
    have hL:= doubled Y f hH
    refine ⟨fun _=>zero_le_one,fun i _=>?_ , ?_,budget_nonneg (hL 0),parentCost S⟩
    · obtain ⟨x,h⟩:= hN i.1; rw [← hY i] at h; exact ⟨x,h,h⟩
    intro x; simp_rw [hY,hh]; convert hL x using 1; ext i; split <;> ring
end YM.QuadraticLocal.Throng
