import YM.FormalOPE.RG10.Rupture.Early
/-!
 # Spending a constant-grade-dependent exponent on traversal moment, before rescale.
 Chose Tier upfront. Does not represent power/Taylor coordinate.Path-spanning assembly later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Rupture
open Function PowerSeries Finset Route Route.Bulk HStein Multi.Vacuum.Gauss Tier Primitives.GCC.LocalPolynomial
open scoped Topology BigOperators Classical
variable (F:Tier)
def tall (n:ℕ) : Tier where
 value x:= F.value x ^ n
 blind:= by rw [F.blind,one_pow]
 near hx hy:= pow_le_pow_left₀ (F.cp hx) (F.near hx hy) _
 toll hx hy:= (pow_le_pow_left₀ (F.cp (add_nonneg hx hy)) (F.toll hx hy) _).trans (le_of_eq (mul_pow ..))
lemma tollLe (n:ℕ) : ∀ x≥0,F.value x ≤ (tall F (n+1)).value x:=fun x hx=> by nth_rw 1 [← pow_one (F.value x)]; exact pow_le_pow_right₀ (F.grade hx) (by omega : 1 ≤ n+1)
variable {I B J X: Type} [Fintype J]
variable (q:I→Row J)(V:Channel (I⊕B))(p:I⊕B→X)
local notation "P"=>Packet (I⊕B)
local notation "W"=>Channel (I⊕B)
local notation "Z"=>Index I B
variable {T: Tape X} (O A E: Lens T) (C L:ℝ)
variable {m n:Index I B} {d i r k:ℕ}
local notation "♥"=>F.value L
local notation "A₁"=> A.m ∘ p
local notation "E₁"=> E.m ∘ p
local notation "w"=> O.m ∘ p
local notation "wB"=> O.m ∘ (p ∘ Sum.inr)
def PaidPair (q:I→Row J)(V:Channel (I⊕B))(T:Tape X)(p:I⊕B→X)(F:Tier)(C L:ℝ)(O A E:Lens T)(r d:ℕ): Prop := ∀ i≤r,∀ m n:Index I B,length m+length n+3*i ≤ d →
     F.value L * F.valueOf (O.m ∘ (p ∘ Sum.inr)) (foot q V i (PowerSeries.C (glyph n)) (glyph m)) ≤ C^(10*d)*(F.face (A.m ∘ p) m * F.face (E.m ∘ p) n)^(d+1)
variable {p q V F C L}
variable (hO: O.m ≤ A.m)(hE: O.m ≤ E.m) (hL:0≤L) (hc:1≤ C) (h : A.Spaced E L)
variable (hh: PaidPair q V T p F C L O A E r d) (hs : k≤ r)(ht:length m+length n+3*k≤d)
include hO hL hc hh hs ht in
lemma lifts (x:B) : let m₁ := Finsupp.single (Sum.inr x) 1 + m;
 ♥ * F.valueOf wB (foot q V k (PowerSeries.C (glyph n)) (glyph m₁)) ≤ C^(10*(d+1))*(F.face A₁ m₁*F.face E₁ n)^(d+1+1):= by
 dsimp only[]; rw [←comma, call, upstairs]
 let m':= Finsupp.single (Sum.inr x) 1 + m; have hj : Sum.inr x∈m'.support:= Finsupp.mem_support_iff.mpr (by unfold m'; simp)
 let P':= F.face A₁ m'*F.face E₁ n; have hu:=F.ready A₁ (nnews A p) m; have hv:=F.ready A₁ (nnews A p) m'; have hw:= F.ready E₁ (nnews E p) n
 have hy: 1≤ P':= (hv.trans (le_mul_of_one_le_right (zero_le_one.trans hv) hw)); have hx:= zero_le_one.trans hy; have hT := F.cp hL
 have hr : F.valueOf wB (MvPolynomial.X x)≤ P':= by rw [MvPolynomial.X, money F wB (nout O p),norm_one,mul_one,level]; exact (((F.near (nout O p x) (hO (p (.inr x)))).trans (F.degree A₁ (nnews A p) m' (Sum.inr x) hj)).trans (le_mul_of_one_le_right (zero_le_one.trans hv) hw))
 apply (mul_le_mul_of_nonneg_left (F.multiplies _ (nout O p) _ _) hT).trans; rw [mul_left_comm];
 apply (mul_le_mul hr (hh k hs m n ht) (mul_nonneg hT (F.lower _ (nout O p) _)) hx).trans
 calc
  P' * _ ≤ P' * (C^(10*(d+1))*P'^(d+1)):= by apply mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ hc (by omega)) (pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hu) (zero_le_one.trans hw)) (mul_le_mul_of_nonneg_right (F.grows A₁ (nnews A p) _ m' le_add_self) (zero_le_one.trans hw)) (d+1)) (pow_nonneg (mul_nonneg (zero_le_one.trans hu) (zero_le_one.trans hw)) _) (pow_nonneg (zero_le_one.trans hc) _)) hx
  _ = _:= by unfold P' m'; rw [pow_succ (n:=d+1)]; ring -- pow_succ order inspect
end YM.FormalOPE.RG10.Rupture
