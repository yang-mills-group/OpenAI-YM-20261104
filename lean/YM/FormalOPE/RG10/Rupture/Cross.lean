import YM.FormalOPE.RG10.Rupture.Price
/-! # Spend traversal at one native mixed root (no extra Γ slack at same site)
   and from early coincidence (inherits budget). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Rupture
open Function PowerSeries Finset Route HStein Tier Multi.Vacuum.Gauss Primitives.GCC.LocalPolynomial
open scoped Topology BigOperators Classical
variable {I B J X: Type} [Fintype J]
variable {q:I→Row J}{V:Channel (I⊕B)}{p:I⊕B→X} {F:Tier}
local notation "P"=>Packet (I⊕B)
local notation "W"=>Channel (I⊕B)
local notation "Z"=>Index I B
variable {T: Tape X} (O A E: Lens T) {C L:ℝ}
variable (m n:Index I B) {d i r k:ℕ}
variable [Fintype I] [DecidableEq I] (a:I)
local notation "A₁"=> A.m ∘ p
local notation "E₁"=> E.m ∘ p
local notation "w"=> O.m ∘ p
local notation "wB"=> O.m ∘ (p ∘ Sum.inr)
local notation "m'"=> Finsupp.single (Sum.inl a) 1+m

def allot (T:Tape X)(F:Tier)(p:I⊕B→X)(C:ℝ)(A E:Lens T)(m n:Index I B)(a:I)(d:ℕ):= C^(10*d)*(F.face (A.m ∘ p) (Finsupp.single (Sum.inl a) 1+m)*F.face (E.m ∘ p) n)^(d+2)
local notation "Zf"=> F.face A₁ (Finsupp.single (Sum.inl a) 1+m)*F.face E₁ n
local notation "Zp"=> allot T F p C A E m n a d
local notation "♥"=>F.value L
variable (hM:Rails q V r p T (tall F (d+1)) C) (he : readyNow q V O p d r C F) (ho : O.m≤ A.m) (hx:O.m≤E.m) (hL:0≤L) (hC:1≤C)(hd:(d:ℝ)≤ C)(hh:PaidPair q V T p F C L O A E r d)
variable (h : A.Spaced E L) (hi:k ≤ r) (ht:length m+length n+3*k ≤ d)
omit [Fintype I] [DecidableEq I] in
lemma product_one (F: Tier)(m n: Index I B)(A E:Lens T)(p:I⊕B→X) :1 ≤ F.face (A.m ∘ p) m * F.face (E.m ∘ p) n:= (F.ready (A.m ∘ p) (nnews A p) m).trans (le_mul_of_one_le_right (F.bright (A.m ∘ p) (nnews A p) m) (F.ready (E.m ∘ p) (nnews E p) n))
include hC
omit [Fintype I] [DecidableEq I] in
lemma land_nn : 0 ≤ allot T F p C A E m n a d :=mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) (pow_nonneg (zero_le_one.trans (product_one ..)) _)
-- from party price opt one term
include hi ht ho hx he h hL hd
omit [Fintype I] in
private lemma bridge (b:I): ♥* F.valueOf wB (opt q V k (glyph m*MvPolynomial.pderiv (.inl b) (glyph n))) ≤ (tall F (d+1)).value (T.Δ (p (.inl a)) (p (.inl b))) * C * Zp:= by
 rw [chop,mul_smul_comm,comma,map_smul, coins,Complex.norm_natCast];
 have hu:0≤ C := zero_le_one.trans hC; let U:=(tall F (d+1)).value (T.Δ (p (.inl a)) (p (.inl b)))
 have hy : 0≤ ♥:= F.cp hL; have hh' : 0≤ Zp:= land_nn A E m n a hC; have hw : 0≤ U:= (tall F _).cp (T.sign ..)
 by_cases h' : b∈ pipes n
 · have hr:= (fine_mem n b).mp h'
   let f:= n-Finsupp.single (.inl b) 1; let z:= m+f;
   have Ht:F.valueOf wB (opt q V k (glyph z)) ≤ C^(6*d)* F.face w z:= he k hi z (by unfold z f; rw [lengths]; have H:=distill hr;omega)
   have hs : F.face w z≤ Zf:= by
     apply (F.max_cost _ (nnews O p) m f).trans; apply max_le
     · have hl := F.near (along_nn (nnews O p) m.support) (mono_along (le_refl _) w A₁ (fun i _=> ho (p i)) (nnews A p))
       exact (le_trans hl (F.grows _ (nnews A p) m (m') le_add_self)).trans (le_mul_of_one_le_right (bright F _ (nnews A p) _) (F.ready _ (nnews E p) n))
     have hl := F.near (along_nn (nnews O p) f.support) (mono_along (le_refl _) w E₁ (fun i _=> hx (p i)) (nnews E p))
     exact (le_trans hl (F.grows _ (nnews E p) f n tsub_le_self)).trans (le_mul_of_one_le_left (bright F _ (nnews E p) _) (F.ready _ (nnews A p) _))
   let x:= p (.inl a); let y:=p (.inl b);
   have h1: 1≤ Zf:= product_one ..; have h0:= zero_le_one.trans h1
   have hg : ♥ ≤ U * Zf:=by
     apply (F.near hL (h x y)).trans; have hw' := T.sign x y
     apply (le_trans (F.toll (add_nonneg (A.sign x) hw') (E.sign y))) _
     have hHX : Sum.inl a∈ (m').support:= Finsupp.mem_support_iff.mpr (by simp)
     have hz₁:= le_trans (F.toll (A.sign x) hw') (mul_le_mul (show F.value (A.m x) ≤ _ from F.degree A₁ (nnews A p) (m') _ hHX) (tollLe F d _ hw') (F.cp hw') (F.bright _ (nnews A p) _))
     have hz₂:= F.degree E₁ (nnews E p) n (Sum.inl b) hr
     exact (mul_le_mul hz₁ hz₂ (F.cp (E.sign y)) (mul_nonneg (F.bright _ (nnews A p) _) hw)).trans (le_of_eq (by unfold U x y at *; ring)) -- maybe fails permutes terms
   have Hb:F.valueOf wB (opt q V k (glyph z))≤ C^(10*d) * Zf := Ht.trans (mul_le_mul (pow_le_pow_right₀ hC (by omega)) hs (F.bright _ (nnews O p) _) (by positivity))
   calc
     _ ≤ (U*(Zf)) * (C*(C^(10*d) * (Zf))) := mul_le_mul hg (mul_le_mul (le_trans (Nat.cast_le.mpr (le_trans (fewer (i:=Sum.inl b) n) (show length n ≤ d by omega))) hd) Hb (Tier.lower _ _ (nout O p) _) hu) (mul_nonneg (Nat.cast_nonneg ..) (Tier.lower _ _ (nout O p) _)) (mul_nonneg hw h0)
     _ = U*C*(C^(10*d)*(Zf)^2):= by ring
     _ ≤ _:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega : 2≤d+2)) (by positivity)) (mul_nonneg hw hu)
 rw [Finsupp.notMem_support_iff.mp (fun he=> h' ((fine_mem n b).mpr he)), Nat.cast_zero,zero_mul,mul_zero]; exact mul_nonneg (mul_nonneg hw hu) hh'

include hM in
theorem joined : ♥ * F.valueOf wB (opt q V k (glyph m * uptick q a (glyph n))) ≤ C*C* Zp:= by
 rw [deriva,mul_sum,map_sum]; apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) (F.cp hL)).trans; rw [mul_sum]
 refine le_trans (b:=(∑ b,travel q p (tall F (d+1)) a b T)* (C * Zp)) ?_ ((mul_le_mul_of_nonneg_right (hM.cov a) (mul_nonneg (zero_le_one.trans hC) (land_nn A E m n a hC))).trans (le_of_eq (mul_assoc ..).symm))
 rw [sum_mul]; apply sum_le_sum; intro b _; rw [mul_smul_comm,map_smul,Tier.coins,mul_left_comm]; apply (mul_le_mul_of_nonneg_left (bridge O A E m n a he ho hx hL hC hd h hi ht b) (norm_nonneg _)).trans; unfold travel; exact le_of_eq (by unfold comp;ring) -- inspect
end YM.FormalOPE.RG10.Rupture
