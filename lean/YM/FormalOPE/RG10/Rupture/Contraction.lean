import YM.FormalOPE.RG10.Rupture.Ancient
/-! # Payment at all ranks compatible substrata. k.Even nonsum path.Vin.
 Expense only polynomial $κ width.Value of F$ along supported routes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Rupture
open Function PowerSeries Finset Route HStein Tier Multi.Vacuum.Gauss Primitives.GCC.LocalPolynomial
open scoped Topology BigOperators Classical
variable {I B J X: Type} [Fintype J] [Fintype I] [DecidableEq I]
variable {q:I→Row J}{V:Channel (I⊕B)}{p:I⊕B→X}{F:Tier}
local notation "P"=>Packet (I⊕B)
local notation "W"=>Channel (I⊕B)
local notation "Z"=> Index I B
variable {T:Tape X} (O A E: Lens T){C L:ℝ}
variable (m n: Index I B)(a:I) {d i r k:ℕ}
local notation "A₁"=> A.m ∘ p
local notation "E₁"=> E.m ∘ p
local notation "w"=> O.m ∘ p
local notation "wB"=> O.m ∘ (p ∘ Sum.inr)
local notation "Zp"=> allot T F p C A E m n a d
local notation "♥"=> F.value L
local notation "B₁"=> Finsupp.single (Sum.inl a) 1 + m
variable (hh:PaidPair q V T p F C L O A E r d)(hM: Rails q V r p T (tall F (d+1)) C)
variable (hV:Guard V r 0) (hV': coeff 0 V=0) (ho:O.m ≤ A.m) (hx:O.m ≤ E.m)(hc:2≤C) (hD : (d:ℝ)≤ C) (hR: (3*(r:ℕ):ℝ)≤ C) (hr:(r+1:ℝ)≤ C)(hL:0≤L)(hz:A.Spaced E L)
include hV hV' ho hx hc hD hR hr hL hz hM hh
private lemma fore (hk:k≤r)(ht:length m + length n+3*k≤d) : ♥ * F.valueOf wB (foot q V k (PowerSeries.C (glyph n)) (glyph B₁)) ≤ C^10 * allot T F p C A E m n a d:= by
 have hC:1 ≤ C:= le_trans (by norm_num) hc
 have h0 := zero_le_one.trans hC; have hZ:= land_nn A E m n a hC (F:=F) (p:=p) (d:=d);
 have hK:0≤ C*C*C := by positivity
 have hy := F.cp hL
 have he := priced O (p:=p) (d:=d) hV hV' (hM.order (tollLe F d)) hc hR hD
 have hh' := joined O A E m n a hM he ho hx hL hC hD hz hk ht -- order inspect
 have hl := (before O A E m n a hL hC hD hh hk ht).trans ((mul_le_mul_of_nonneg_right (hM.plain a) (mul_nonneg h0 hZ)).trans (le_of_eq (mul_assoc ..).symm)) -- order
 let S (j:ℕ×ℕ) := foot q V j.2 (PowerSeries.C (glyph n)) (uptick q a (coeff j.1 V)*glyph m)
 have hH : ♥ * F.valueOf wB (∑ j∈antidiagonal k,S j) ≤ C * (C*C*C*Zp):= by
    apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) hy).trans; rw [mul_sum]
    apply le_trans (b:=∑ _∈antidiagonal k, C*C*C*Zp) (sum_le_sum (fun j hj=> reused O A E m n a hM hL hC hh hk ht hR hV _ _ (mem_antidiagonal.mp hj)))
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ _=>C*C*C*Zp), sum_const,nsmul_eq_mul,card_range]; push_cast; exact mul_le_mul_of_nonneg_right ((add_le_add_left (Nat.cast_le.mpr hk) 1).trans hr) (mul_nonneg hK hZ)
 rw [←comma,call,bushes q V _ _ _ a hV']; apply (mul_le_mul_of_nonneg_left (F.plus _ (nout O p) _ _) hy).trans; rw [mul_add]
 apply le_trans (add_le_add (b:=C*C*Zp+C*(C*C*C*Zp)) ((mul_le_mul_of_nonneg_left (F.plus _ (nout O p) _ _) hy).trans _ ) hh'); swap; -- placeholder expects goal
 · rw [mul_add]; exact add_le_add hl hH
 apply le_trans (b:= (C^4+C^4+C^4)*Zp) _
 · apply mul_le_mul_of_nonneg_right _ hZ
   nlinarith [show C^6 ≤ C^10 from pow_le_pow_right₀ hC (by norm_num), mul_le_mul_of_nonneg_right (show 4≤C^2 by nlinarith) (pow_nonneg h0 4)] -- might unsolv elimination of high exponent
 rw [add_mul,add_mul]; have hu : C * C * Zp ≤ C^4 * Zp:= mul_le_mul_of_nonneg_right ((sq C).symm.le.trans (pow_le_pow_right₀ hC (by norm_num))) hZ -- inspect
 exact add_le_add (add_le_add hu (le_of_eq (by ring))) hu
lemma paid_step : PaidPair q V T p F C L O A E r (d+1):= by
 intro k hk m n ht
 obtain hu|hu:= eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp hu,show glyph (0:Z)=(1:P) from rfl, stable_row,Tier.zero,mul_zero]; exact mul_nonneg (pow_nonneg (le_trans (by norm_num) hc) _) (pow_nonneg (zero_le_one.trans (product_one ..)) _)
 obtain ⟨a,ha⟩:= hu
 let U := m-Finsupp.single a 1; have he : m= Finsupp.single a 1+ U:= Eq.symm ((add_comm _ U).trans (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp ha)))
 have hA:length U+length n+3*k ≤ d:= by unfold U; have hy:= distill ha; omega
 rw [he]; cases a with
 | inl i=> exact (fore O A E U n i hh hM hV hV' ho hx hc hD hR hr hL hz hk hA).trans (le_of_eq (by unfold allot; rw [Nat.mul_add, Nat.mul_one,pow_add]; ring_nf)) -- ring nf Nat?
 | inr i=> exact lifts O A E ho hL (le_trans (by norm_num) hc) hh hk hA i
omit hh
lemma paid : PaidPair q V T p F C L O A E r d:= by
 induction d with
 | zero=>
   intro i hi m n hm; have hx : m=0:= by ext a; have he:=fewer (i:=a) m; simpa using (show m a=0 by omega);
   rw [hx,show glyph (0: Z)=(1:P) from rfl, stable_row,Tier.zero,mul_zero]; simpa [Tier.silent] using (F.bright _ (nnews E p) n)
 | succ d ih=>
   push_cast at hD; have hd' : (d:ℝ)≤C:= by linarith
   have he:= hM.order (G:=tall F (d+1)) (fun _ hx=>pow_le_pow_right₀ (F.grade hx) (Nat.le_succ (d+1))) -- inspect
   exact paid_step O A E (ih he hd') he hV hV' ho hx hc hd' hR hr hL hz
end YM.FormalOPE.RG10.Rupture
