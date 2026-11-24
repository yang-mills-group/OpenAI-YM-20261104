import YM.OPE.Mountains.Billboard
import YM.OPE.Trees.Errors
/-! # Wallet pricing for any finite horizon tree.

`GrowthG` is allowed to fund the leading grace factor or any convenient
smaller amount. Thus retire intermediate vertices without repeatedly choosing
coefficient conventions or even new error rates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Mountain
open Function Filter Finset OPE.Log Portrait Trunk
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} (hP:P.Coherent)
variable (H:Services C F S) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (hf:φ ≤ F.fuse)
    {W r d}(V:LogPackage C W r d) (hG:MatrixTicket (C:=C) S U.sector.derivatives φ)
variable {I J:Type}[Fintype I] {s:Arboreal I} {χ:Ultrafilter J} {t:I→ℝ}
    {x:J→I→ E4}{R:J→I→ℝ}{M δ:ℝ}{i j k o:I} {a b : Finset I}
    (p:I→ C.book.Token) (D:I→ℕ) (w:Mode U.sector.derivatives)
variable (h:s.Coterie (χ:Filter J) t M δ x R) (ht:s.Active a)
local notation "T!"=> (fun i=>s.fullLife (R i))
local notation "u!"=> (fun j=> s.fee p (R j) (s.live a) s.root w.fst)
local notation "L"=> U.sector.derivatives
def GrowthG (s:Arboreal I)(φ:Filter J)(R:J→ I→ℝ)(D:I→ℕ)(a:Finset I)(W:J→ℝ): Prop:= ∀ i∈ s.middle a, Wallet φ (fun i=>s.fullLife (R i)) (fun j=> (s.ratioAt (R j) i)^(D i+1)*W j)
include V H hf h hG hP ht
lemma fullNest {W:J→ℝ} (hW:GrowthG s χ R D a W) : Wallet (χ:Filter J) T! (fun i=> (u! i* W i) • (coalesce P (s.live a) (x i) p s.root w-factorization P s a (x i) p w D)):=by
    induction hN:a.card using Nat.strong_induction_on generalizing a p with | h n ih
    by_cases hp:s.middle a=∅
    · apply (Wallet.const h.time (0:ℂ)).congr; filter_upwards with i; rw [Nest.staging P (x i) w ht hp,sub_self,smul_zero]
    obtain ⟨i,hi,he⟩:= terminals (nonempty_iff_ne_empty.mpr hp); let b':=s.redact a i; have hb : s.Active b':= redacted ht hi; let q' j:= s.fee p (R j) (s.live a) s.root w.fst; let u j:=q' j* W j; let p'(w:Mode L):= update p i (P.letter w); let f(j:J)(a)(p):= coalesce P (s.live a) (x j) p s.root w; let F j:= s.alter P a p x i (D i) f j
    let B j:= R j (s.parent i)/R j i; have hY:= upon_border U hP H hf V hG p (D i) w h ht hi he; have hx : Wallet (χ:Filter J) T! (fun j=> u j • F j):=by
       apply ((hW i hi).smul hY).congr; filter_upwards [(ratio_rate h.tracked (ht.included (mem_erase.mp hi).2)).pos] with j hj; rw [← mul_smul]; change _ • F j=u j • F j; have hu : (R j (s.parent i)/R j i)=(s.ratioAt (R j) i)⁻¹:= (inv_div ..).symm; rw [hu]; rw [inv_pow]; congr 1; unfold u q'; field_simp
    let C'(w':Mode L)(j):=coalesce P (s.inputs a i) (x j) p i w'; let G(w': Mode L)(j):= factorization P s b' (x j) (p' w') w D
    have hu (w':Mode L): Wallet (χ:Filter J) T! (fun j=> u j • ( C' w' j * (f j b' (p' w') - G w' j))):= multiply_cash p w.fst h ht hi (P.letter w') (localFee U hP H hf V hG p w' h ht (mem_erase.mp hi).2 (Subset.refl ..)) (ih _ (hN ▸ redact_gains (mem_erase.mp hi).2) (p' w') hb (fun k hk=> hW k ((erase_subset_erase _ (redacting (mem_erase.mp hi).2)) hk)) rfl)
    apply (hx.add h.time (Wallet.sum h.time (s:=bands L (D i)) (fun w _=>hu w))).congr; filter_upwards with j
    rw [Nest.contracted P he hi]; let S':= bands L (D i); change u j • F j + ∑ w∈ S', (u j • (C' w j* (f j b' (p' w) -G w j))) = u j • (f j a p- ∑ w∈ S', C' w j * G w j); rw [← smul_sum,← smul_add]; congr 1; unfold F alter; simp_rw [mul_sub,sum_sub_distrib]; abel!

omit ht V H hf hG hP
-- eq price: allows division also zero grace.Leading exact sum to restore via stage.
include h
lemma grace_before {j:J} (hp:s.Graduated (R j))(hi:i∈ s.middle s.zones): (s.ratioAt (R j) i)^(D i+1) ≤ s.grace (R j) D:= single_le_sum (fun k hk=> pow_nonneg (div_pos (hp.allowed k (mem_erase.mp hk).2) (hp.allowed _ (s.inward k)) |>.le) (D k+1)) hi
lemma scored (he:(s.middle s.zones).Nonempty) : ∀ᶠ j in χ,0<s.grace (R j) D:=by
    obtain ⟨i,hi⟩:= he; filter_upwards [(ratio_rate h.tracked (mem_erase.mp hi).2).pos,h.space] with j hj he using lt_of_lt_of_le (pow_pos hj _) (grace_before D h he.sizes hi)
lemma whole_fuel : GrowthG s χ R D s.zones (fun j=> (s.grace (R j) D)⁻¹):=by
    intro i hi
    apply (Wallet.const h.time (1:ℝ)).of_le'; all_goals filter_upwards [scored D h ⟨i,hi⟩,(ratio_rate h.tracked (mem_erase.mp hi).2).pos,h.space] with j hj he h'
    · exact mul_pos (pow_pos he _) (inv_pos.mpr hj)
    rw [← div_eq_mul_inv]; exact (div_le_one hj).2 (grace_before D h h'.sizes hi)
end YM.OPE.Arboreal.Mountain
