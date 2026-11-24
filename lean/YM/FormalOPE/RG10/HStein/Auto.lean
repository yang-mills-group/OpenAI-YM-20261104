import YM.FormalOPE.RG10.HStein.Price
/-! # Road estimates for Stein transmissions: one skeleton and one added leg -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Route Route.Bulk PowerSeries Function MeasureTheory Metric Filter Topology Finset
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J Y:Type} [Fintype J]
open Primitives.GCC.LocalPolynomial (length)
section letters
variable {i: I}
lemma comma (m n:Letters I): glyph m*glyph n=glyph (m+n):= by simp [glyph, MvPolynomial.monomial_mul]
lemma echo (c:ℂ)(m:Letters I): MvPolynomial.monomial m c= c • glyph m:= by unfold glyph; rw [MvPolynomial.smul_monomial]; simp
lemma lengths (m n:Letters I): length (m+n) = length m+length n:= by unfold length; rw [Finsupp.sum_add_index'] <;> simp -- inspect
lemma simple (a:I): length (Finsupp.single a 1)=1:= by simp [length]
lemma distill {m:Letters I} (h : i∈ m.support): length (m-Finsupp.single i 1)+1=length m:= by nth_rw 2 [← simple i]; rw [← lengths, Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp h)] -- rewrites both ones issue
lemma fewer (m:Letters I) : m i ≤ length m := by
 by_cases h:i∈m.support
 · exact single_le_sum (f:=fun i=>m i) (fun i _=> Nat.zero_le (m i)) h
 · rw [Finsupp.notMem_support_iff.mp h]; exact Nat.zero_le _
lemma call (a:I): glyph (Finsupp.single a 1)= MvPolynomial.X a:= rfl
lemma resolves (X:Packet I): X=∑ m∈X.support,MvPolynomial.coeff m X • glyph m:= by
 nth_rw 1 [X.as_sum]; simp_rw [echo]
lemma chop (c:Letters I)(a:I): MvPolynomial.pderiv a (glyph c)=(c a : ℂ) • glyph (c-Finsupp.single a 1):= by rw [← echo,glyph,MvPolynomial.pderiv_monomial,one_mul]
end letters

open Tier
variable (q : I→Row J) (V : Channel (I⊕ B)) {T : Tape Y} (O:Lens T) (p:I ⊕ B → Y) (F:Tier) (C:ℝ)
local notation "A"=> Index I B
local notation "P"=> p ∘ Sum.inl
local notation "M" => O.m ∘ p
lemma nnews : 0 ≤ M:= fun _=> O.sign _
lemma nout : 0 ≤ O.m ∘ (p ∘ Sum.inr):= fun _=> O.sign _
-- output charge needed for full step
lemma driven (x y:I)(m n:A)(u:y∈pipes n): F.face M n ≤ F.face M (Finsupp.single (Sum.inl x) 1+m) * F.value (T.Δ (P x) (P y)) * F.value (diam p n T):= by
 let v:= F.face M (Finsupp.single (Sum.inl x) 1+m); change _ ≤ v*_ *_
 have hx : F.value (O.m (P x)) ≤ v := by unfold v; have he:= grows F _ (nnews O p) _ (Finsupp.single (Sum.inl x) 1+m) (show Finsupp.single (Sum.inl x) 1 ≤ Finsupp.single (Sum.inl x) 1+m from le_self_add); rw [level] at he; exact he
 have ho:=F.cp (T.sign (P x) (P y)); have hz:= F.cp (diam_nn p n (T:=T));
 change F.value _ ≤ _
 refine (F.near (along_nn (nnews O p) n.support) (along_le M n.support ?_ (fun i hi=> show M i ≤ (O.m (P y))+diam p n T from (O.path _ _).trans (by gcongr; exact diam_ge p n ((fine_mem n y).mp u) hi)) )).trans ?_
 · exact add_nonneg (O.sign _) (diam_nn ..)
 exact (F.toll (O.sign _) (diam_nn ..)).trans (mul_le_mul_of_nonneg_right ((F.near (O.sign (P y)) (O.path (P y) (P x))).trans ((F.toll (O.sign _) (T.sign ..)).trans (mul_le_mul_of_nonneg_right hx ho))) hz)
lemma dialed (x y:I)(m n:A)(u:y∈pipes n): F.face M ((n-Finsupp.single (.inl y) 1)+m) ≤ F.face M (Finsupp.single (Sum.inl x) 1+m) * F.value (T.Δ (P x) (P y)) * F.value (diam p n T):= by
 apply (max_cost F M (nnews O p) _ _).trans
 apply max_le
 · exact (grows F M (nnews O p) _ _ tsub_le_self).trans (driven O p F x y m n u)
 refine ((grows F M (nnews O p) _ _ le_add_self).trans (le_mul_of_one_le_right ?_ (F.grade (T.sign ..)))).trans (le_mul_of_one_le_right ?_ (F.grade (diam_nn ..)))
 exacts [bright F M (nnews O p) _, mul_nonneg (bright F M (nnews O p) _) (F.cp (T.sign ..))] -- inspect

lemma main (a b:I) : ‖score q b a‖=crossing q a b:= by rw [score, crossing, Complex.norm_real, Real.norm_eq_abs]; congr 1; unfold crossed; exact sum_congr rfl fun _ _=> mul_comm ..
local notation "W"=> Packet (I⊕B)
-- F supply
variable [Fintype I] [DecidableEq I]
def cash (T : Tape Y) (z: Packet (I⊕ B)) (y:I):= ∑ n∈z.support.filter (fun n=> y∈pipes n), F.value (diam p n T) * ‖MvPolynomial.coeff n z‖

def travel (a b:I) (T:Tape Y):= ‖score q b a‖ * F.value (T.Δ (P a) (P b))
structure Rails (q : I→Row J)(V:Channel (I⊕B))(r:ℕ)(p:I⊕B→Y)(T:Tape Y)(F:Tier)(C:ℝ): Prop where
 cov (a:I): ∑ b, travel q p F a b T ≤ C
 add {i:ℕ}: i ≤ r → ∀ b, cash p F T (coeff i V) b ≤ C

variable {r d n k:ℕ}
local notation "Z" => Rails q V r p T F C
variable {q V p F C}
lemma Rails.order {G:Tier}(h:Rails q V r p T F C) (hg:∀ x≥0,G.value x ≤ F.value x): Rails q V r p T G C:= by
 refine ⟨fun i=>(sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hg _ (T.sign (P i) (P j))) (norm_nonneg (score q j i)))).trans (h.cov i),fun hv i=>(sum_le_sum (fun j hj=>?_)).trans (h.add hv i)⟩
 exact mul_le_mul_of_nonneg_right (hg _ (diam_nn ..)) (norm_nonneg _)
lemma Rails.noFare (h:Rails q V r p T F C): Rails q V r p T free C:= h.order (fun _ hx=> by rw [free_stamp]; exact F.grade hx)
lemma Rails.plain (h:Rails q V r p T F C)(i:I): ∑ j, ‖score q j i‖ ≤ C:= by simpa [travel] using h.noFare.cov i
lemma stem (h: schur p q T n C)(u:Binary.vacuum V p C r n T): Rails q V r p T (pol n) C:= by
 refine ⟨fun i=>?_, fun hi b=> u _ hi b⟩; apply le_trans _ (h i); apply sum_le_sum; intro j _; rw [travel, main, mul_comm]; rfl
end YM.FormalOPE.RG10.HStein
