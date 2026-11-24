import YM.FormalOPE.RG10.HStein.Auto
/-! # Stein append bound from one vertex with exponent headroom

 Conditional Wick derivative either drops an inherited generator or attaches one vacuum vertex
 with credit. NO hypotheses on marked correlations or conditional forms. Inputs local paper
 norms on each geometric vacancy/time. Covers every volume (finite) whose centered stationary
 Gaussian step is represented in given gauge with all post-factor moment and endpoint budgets
 supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Route Route.Bulk PowerSeries Function Finset Beams
open Multi.Vacuum.Gauss
open Tier Primitives.GCC.LocalPolynomial
open scoped Topology BigOperators Classical
variable {I B J Y:Type} [Fintype J]
local notation "Z"=> Index I B
local notation "P"=> Packet (I⊕B)
local notation "X"=> MvPolynomial.X
variable {q:I→Row J} {V :Channel (I⊕B)} {T:Tape Y} {p:I⊕B→Y} {F:Tier} {C:ℝ} {r d k:ℕ}

variable (O:Lens T)
local notation "A"=> O.m ∘ p
local notation "Γ"=> O.m ∘ (p ∘ Sum.inr)

def readyNow (q:I→Row J)(V :Channel (I⊕B))(O:Lens T)(p:I⊕B→Y)(d r:ℕ)(C:ℝ)(F:Tier) : Prop := ∀ k≤r,∀ m:Z,length m+3*k≤d → F.valueOf (O.m ∘ (p ∘ Sum.inr)) (opt q V k (glyph m)) ≤ C^(6*d)*F.face (O.m ∘ p) m
-- uniform by prepared rank k; top not taken pointwise
variable (U: readyNow q V O p d r C F) (hV : Guard V r 0)
variable [Fintype I] [DecidableEq I]
variable (B₀:Rails q V r p T F C) (hc : 1≤C) (hr:(3*(r:ℕ):ℝ)≤C) (hd:(d:ℝ) ≤ C) (hk:k ≤ r)
variable (m : Index I B) (hm:length m+3*k≤d) (a b : I)
local notation "Y₀" => Finsupp.single (Sum.inl a) 1+m
local notation "M" => C^(6*d)*F.face A Y₀

include hV hr hm hk U hc in
omit [Fintype I] [DecidableEq I] in
private theorem timing (i j:ℕ)(h:i+j=k) (n: Index I B) (hn:n∈ (coeff i V).support) (ht:b∈pipes n) : F.valueOf Γ
  (opt q V j ( (MvPolynomial.coeff n (coeff i V)) • MvPolynomial.pderiv (.inl b) (glyph n) * glyph m))
  ≤ (F.value (diam p n T) * ‖MvPolynomial.coeff n (coeff i V)‖) * (F.value (T.Δ (p (.inl a)) (p (.inl b))) * C * M):= by
 have ht := (fine_mem n b).1 ht
 have he:= distill ht; have hl := (show length n ≤ _ from MvPolynomial.le_totalDegree hn).trans (hV i (by omega));
 have hr': (↑(n (.inl b)):ℝ) ≤ C:=by
     norm_cast at hr ⊢ -- inspect
     have hv : (n (.inl b)) ≤ 3*r:= (fewer n).trans (by omega); exact (Nat.cast_le.mpr hv).trans hr -- cast rewrite
 let R:= (n-Finsupp.single (.inl b) 1)+m
 let c:= MvPolynomial.coeff n (coeff i V)
 simp_rw [smul_mul_assoc, chop,smul_mul_assoc, comma,_root_.map_smul,coins,Complex.norm_natCast]
 have H₀ : F.valueOf Γ (opt q V j (glyph R)) ≤ _:= U j (by omega) R (by unfold R; rw [lengths]; omega)
 have H : 0 ≤ C:= zero_le_one.trans hc
 have hx:= bright F A (nnews O p) Y₀; have hy:= F.cp (diam_nn p n (T:=T)); have hz:= F.cp (T.sign (p (.inl a)) (p (.inl b)))
 calc
  ‖c‖ * ((↑(n (.inl b)):ℝ) * _) ≤ ‖c‖*(C*(C^(6*d)* F.face A R)) := by exact mul_le_mul_of_nonneg_left (mul_le_mul hr' H₀ (Tier.lower F Γ (nout O p) _) H) (norm_nonneg c)
  _ ≤ ‖c‖*(C*(C^(6*d)* (F.face A Y₀ * F.value (T.Δ (p (.inl a)) (p (.inl b))) * F.value (diam p n T)))):= by gcongr; exact dialed O p F a b m n ((fine_mem n b).mpr ht)
  _ = _ := by unfold c; ring
include U hV B₀ hc hr hk hm in
theorem release (i j:ℕ)(h:i+j=k) : F.valueOf Γ (opt q V j ((uptick q a (coeff i V))*glyph m)) ≤ (C*C*C)*M := by
 let x (b:I):= F.value (T.Δ (p (.inl a)) (p (.inl b)))
 have Z₀ : 0≤ C:= zero_le_one.trans hc; have hz:= bright F A (nnews O p) Y₀; have hm' : 0≤ M := by positivity
 let A₀:=(coeff i V).support
 have content (b:I): F.valueOf Γ (opt q V j ((MvPolynomial.pderiv (.inl b) (coeff i V))*glyph m)) ≤ C * (x b * C * M) := by
    let v:=coeff i V; let R n:=MvPolynomial.coeff n v; let B:= A₀.filter (fun n=> b∈pipes n)
    have he : MvPolynomial.pderiv (.inl b) (coeff i V)=∑ n∈B, R n • MvPolynomial.pderiv (.inl b) (glyph n):= by
       nth_rw 1 [resolves (coeff i V)]; rw [map_sum] -- may fail
       simp_rw [Derivation.map_smul]; symm; apply sum_subset (filter_subset ..); intro n hn hb
       rw [chop, Finsupp.notMem_support_iff.mp (show Sum.inl b ∉ n.support from fun ht=> hb (mem_filter.mpr ⟨hn,(fine_mem n b).mpr ht⟩)),Nat.cast_zero,zero_smul,smul_zero]
    rw [he,sum_mul,map_sum]; apply (many F Γ (nout O p) _ _).trans
    refine (le_trans (b:=(cash p F T (coeff i V) b)*(x b * C*M)) ?_ (mul_le_mul_of_nonneg_right (B₀.add (by omega) _) (by have ht:= F.cp (T.sign (p (.inl a)) (p (.inl b))); unfold x; positivity)))
    rw [cash,sum_mul]; exact sum_le_sum fun n hn => timing O U hV hc hr hk m hm a b i j h n (mem_filter.mp hn).1 (mem_filter.mp hn).2 -- inspect
 rw [deriva,sum_mul,map_sum]; apply (many F Γ (nout O p) _ _).trans
 refine le_trans (b:=(∑ b,travel q p F a b T)*(C * C * M)) ?_ ((mul_le_mul_of_nonneg_right (B₀.cov a) (by positivity)).trans (le_of_eq (by ring)))
 rw [sum_mul]; apply sum_le_sum;intro b _; rw [smul_mul_assoc, map_smul, coins]; apply (mul_le_mul_of_nonneg_left (content b) (norm_nonneg _)).trans; unfold travel x; simp only [Function.comp_apply]; exact le_of_eq (by ring)
include U B₀ hc hd hk hm in
theorem early : F.valueOf Γ (opt q V k (uptick q a (glyph m))) ≤ C*C*M:= by
 rw [deriva,map_sum]; apply (many F Γ (nout O p) _ _).trans
 have h0:0≤C:= zero_le_one.trans hc; have hu := bright F A (nnews O p) Y₀; have hp : 0≤ M:= by positivity
 apply le_trans (b:=(∑ b,‖score q b a‖)*(C*M)) _ ((mul_le_mul_of_nonneg_right (B₀.plain a) (by positivity)).trans (le_of_eq (by ring)))
 rw [sum_mul]; apply sum_le_sum; intro b _; rw [_root_.map_smul,coins]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 rw [chop, _root_.map_smul,coins,Complex.norm_natCast]; by_cases h:b∈ pipes m
 · let w := m-Finsupp.single (.inl b) 1; have he:= distill ((fine_mem m b).mp h); have hl:= (show m (.inl b) ≤ length m from fewer _).trans (by omega : length m ≤ d)
   apply mul_le_mul ((Nat.cast_le.mpr hl).trans hd) _ (Tier.lower F _ (nout O p) _) h0
   exact (U k hk w (by unfold w; omega)).trans (mul_le_mul_of_nonneg_left (grows F A (nnews O p) _ _ (tsub_le_self.trans le_add_self)) (by positivity)) -- careful m ≤ single+m notation le_add_self
 rw [Finsupp.notMem_support_iff.mp (fun h₁=> h ((fine_mem m b).mpr h₁)), Nat.cast_zero,zero_mul]; positivity
end YM.FormalOPE.RG10.HStein
