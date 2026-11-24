import YM.FormalOPE.RG10.Rupture.Cross
/-! # Ancestor & early attachment prices. -/
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

local notation "Zf"=> F.face A₁ (Finsupp.single (Sum.inl a) 1+m)*F.face E₁ n
local notation "Zp"=> allot T F p C A E m n a d
local notation "♥"=>F.value L
variable (hM:Rails q V r p T (tall F (d+1)) C) (he : readyNow q V O p d r C F) (ho : O.m≤ A.m) (hx:O.m≤E.m) (hL:0≤L) (hC:1≤C)(hd:(d:ℝ)≤ C)(hh:PaidPair q V T p F C L O A E r d)
variable (h : A.Spaced E L) (hi:k ≤ r) (ht:length m+length n+3*k ≤ d)
include hh ht hi hC hd hL
lemma before : ♥* F.valueOf wB (foot q V k (PowerSeries.C (glyph n)) (uptick q a (glyph m))) ≤ (∑ b, ‖score q b a‖)* (C* Zp) := by
 have hy := F.cp hL; have h0:= zero_le_one.trans hC; have hh' := land_nn A E m n a hC (F:=F) (p:=p) (d:=d)
 rw [deriva,map_sum,sum_mul]; apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) hy).trans; rw [mul_sum]; apply sum_le_sum; intro b _; rw [map_smul,Tier.coins,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 rw [chop,map_smul,Tier.coins,Complex.norm_natCast,mul_left_comm]; by_cases he₁:b ∈ pipes m
 · let U:=m-Finsupp.single (Sum.inl b) 1
   have hr:= distill ((fine_mem m b).mp he₁); have hu:U ≤ m':= tsub_le_self.trans le_add_self;
   have he':♥*F.valueOf wB (foot q V k (PowerSeries.C (glyph n)) (glyph U)) ≤ Zp:= by
      unfold allot; refine (hh k hi U n (by unfold U; omega)).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 _));
      exact (pow_le_pow_left₀ (zero_le_one.trans (product_one ..)) (mul_le_mul_of_nonneg_right (F.grows _ (nnews A p) U _ hu) (F.bright _ (nnews E p) n)) _).trans (pow_le_pow_right₀ (product_one ..) (by omega))
   refine le_trans (mul_le_mul_of_nonneg_left he' (by positivity : (0:ℝ) ≤ (m (Sum.inl b)))) (mul_le_mul_of_nonneg_right (le_trans (Nat.cast_le.mpr ((fewer _).trans (by omega))) hd) hh')
 rw [Finsupp.notMem_support_iff.mp (fun he=> he₁ ((fine_mem m b).mpr he)),Nat.cast_zero,zero_mul]; exact mul_nonneg h0 hh'
omit hd
variable (hr:(3*(r:ℕ):ℝ)≤C)(hV:Guard V r 0)
local notation "Bf"=> tall F (d+1)
include hr hV
omit [Fintype I] [DecidableEq I] in
private theorem styles (i j:ℕ)(h:i+j=k)(b:I)(y: Z)(hy:y∈ (coeff i V).support)(hn:b∈pipes y) : ♥* F.valueOf wB
   (foot q V j (PowerSeries.C (glyph n)) ((MvPolynomial.coeff y (coeff i V)) • MvPolynomial.pderiv (.inl b) (glyph y)*glyph m)) ≤ ((Bf).value (diam p y T)* ‖MvPolynomial.coeff y (coeff i V)‖)* ((Bf).value (T.Δ (p (.inl a)) (p (.inl b))) * (C* Zp)):= by
 let x:= (y-Finsupp.single (Sum.inl b) 1)+m
 have h0 := zero_le_one.trans hC; have h0' := F.cp hL
 have hx :=F.cp (diam_nn p y (T:=T)); have hz:=F.cp (T.sign (p (.inl a)) (p (.inl b))); have ht1:=F.bright A₁ (nnews A p) (m'); have ht2:=F.bright E₁ (nnews E p) n
 have hm := (show length y ≤ _ from MvPolynomial.le_totalDegree hy).trans (hV i (by omega)); have ht3:length x+length n+3*j ≤ d:=by unfold x; rw [lengths]; have he:= distill ((fine_mem y b).mp hn); omega
 let A':=((Bf).value (diam p y T)* (Bf).value (T.Δ (p (.inl a)) (p (.inl b))))
 have he : (F.face A₁ x*F.face E₁ n)^(d+1) ≤ A'*(Zf)^(d+2):= by
    let a' := F.value (diam p y T); let b':= F.value (T.Δ (p (.inl a)) (p (.inl b)))
    have hl:F.face A₁ x*F.face E₁ n ≤ (a'*b')*(Zf):= (mul_le_mul_of_nonneg_right (dialed A p F a b m y hn) ht2).trans (le_of_eq (by dsimp only [a',b',comp]; ring))
    have hU : A'= (a'*b')^(d+1):= by rw [mul_pow]; rfl
    apply (pow_le_pow_left₀ (zero_le_one.trans (product_one ..)) hl (d+1)).trans; rw [mul_pow,hU]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (product_one ..) (by omega : d+1≤d+2)) (pow_nonneg (mul_nonneg hx hz) _ )
 let ψ:= foot q V j (PowerSeries.C (glyph n)) (glyph x); have hA:0 ≤ A':=mul_nonneg ((Bf).cp (diam_nn ..)) ((Bf).cp (T.sign ..)); have hℓ:=land_nn A E m n a hC (F:=F) (p:=p) (d:=d)
 have hk : ♥* F.valueOf wB ψ ≤ A'*Zp:= ((hh j (by omega) x n ht3).trans (mul_le_mul_of_nonneg_left he (pow_nonneg h0 _))).trans (le_of_eq (by unfold allot; ring))
 have hF : (↑(y (.inl b)):ℝ) ≤ C:=by norm_cast at hr ⊢; exact (Nat.cast_le.mpr ((fewer _).trans (by omega))).trans hr
 let v := MvPolynomial.coeff y (coeff i V); have h1 : 0 ≤ (↑(y (.inl b)):ℝ):= by positivity
 simp_rw [chop, smul_mul_assoc, comma, map_smul, Tier.coins,Complex.norm_natCast];
 calc
   ♥ * (‖v‖ * (↑(y (.inl b))*_)) = (‖v‖ * ↑(y (.inl b))) * (♥*F.valueOf wB ψ):= by dsimp only [ψ,x]; ring
   _ ≤ (‖v‖ * C) * (A'* Zp):= mul_le_mul (mul_le_mul_of_nonneg_left hF (norm_nonneg v)) hk (mul_nonneg h0' (F.lower _ (nout O p) ψ)) (by positivity)
   _ = _:= by unfold A' v; ring
include hM
lemma reused (i j:ℕ)(h:i+j=k) : ♥* F.valueOf wB (foot q V j (PowerSeries.C (glyph n)) ((uptick q a (coeff i V))* glyph m)) ≤ (C*C*C)* Zp:= by
 let W₀ := fun b:I=> (Bf).value (T.Δ (p (.inl a)) (p (.inl b))); have hw b:0 ≤ W₀ b:= (Bf).cp (T.sign ..); have hT := land_nn A E m n a hC (F:=F) (p:=p) (d:=d);
 have ha:= F.cp hL; have hB:=zero_le_one.trans hC; let X (b:I) := cash p Bf T (coeff i V) b
 have hx (b:I): ♥* F.valueOf wB (foot q V j (PowerSeries.C (glyph n)) ((MvPolynomial.pderiv (.inl b) (coeff i V))*glyph m)) ≤ C * (W₀ b*(C*Zp)):= by
    let Z₀:= (coeff i V).support; let Y:= Z₀.filter (fun y=> b∈pipes y); let f y:= MvPolynomial.coeff y (coeff i V) • MvPolynomial.pderiv (.inl b) (glyph y)
    have hU: MvPolynomial.pderiv (.inl b) (coeff i V)=∑ y∈Y,f y:= by nth_rw 1 [resolves (coeff i V)];rw [map_sum]; simp_rw [Derivation.map_smul]; symm; apply sum_subset (filter_subset ..); intro y hy hv; unfold f; rw [chop,Finsupp.notMem_support_iff.mp (fun hn=>hv (mem_filter.mpr ⟨hy, (fine_mem y b).mpr hn⟩))]; simp
    have hl:= hw b
    rw [hU,sum_mul, map_sum]; apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) ha).trans; rw [mul_sum]; apply le_trans (b:= X b * (W₀ b*(C*Zp))) _ (mul_le_mul_of_nonneg_right (hM.add (by omega) b) (by positivity)); unfold X cash; rw [sum_mul]; apply sum_le_sum; intro y hy;
    exact styles O A E m n a hL hC hh hi ht hr hV i j h b y (mem_filter.mp hy).1 (mem_filter.mp hy).2
 rw [deriva,sum_mul,map_sum]; apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) ha).trans; rw [mul_sum]; apply le_trans (b:=(∑ b,travel q p Bf a b T)*(C*(C*Zp))) _ ((mul_le_mul_of_nonneg_right (hM.cov a) (by positivity)).trans (le_of_eq (by ring))); rw [sum_mul]; apply sum_le_sum;intro b _; rw [smul_mul_assoc,map_smul,Tier.coins,mul_left_comm]; apply (mul_le_mul_of_nonneg_left (hx b) (norm_nonneg _)).trans; exact le_of_eq (by unfold W₀ travel comp;ring)
end YM.FormalOPE.RG10.Rupture
