import YM.FormalOPE.RG10.HStein.Pound
/-! # No loss of output rooted moment in generic substitution

 For each homogeneous packet on I, plugging through-order channels on B. Later gradient
 subtraction with P_coupling compatible. Tight input factor (when it can be <1 converts decrement).
 Depends on exponential parameters and poses solely through the hypotheses (each generator, both
 matched moment relative declared lens and plain). Then instantiate on rough single step.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Route Route.Bulk PowerSeries
open MvPolynomial (totalDegree aeval)
open Finset Function Tier
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J Y:Type} {T:Tape Y}
section pay
variable {A:I→ℝ}{O:B→ℝ}
variable {M:ℝ} {w : I→ Channel B} {F:Tier}
variable {k l n d:ℕ}

def Targeted (F:Tier)(A:I→ℝ)(O:B→ℝ)(w:I→Channel B)(k:ℕ)(M:ℝ): Prop := ∀ i,F.gain O (w i) k ≤ F.value (A i) * M
variable (hO:0≤O) (hA:0≤A) (U:Targeted F A O w k M) (u:Targeted free A O w k M)(hM:0≤M)
local notation "L"=> Primitives.GCC.LocalPolynomial.length
local notation "Q"=> aeval w
include hO hM u
private lemma straight (m:Letters I):free.gain O (Q (glyph m)) k ≤ M ^ L m := by
 obtain he|he:= eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp he]; simp only [show L (0:Letters I)=0 from rfl, show glyph (0: Letters I)=1 from rfl, map_one,pow_zero, Tier.once]; rfl
 obtain ⟨i,hi⟩:= he
 let t:=m-Finsupp.single i 1; have h : m=t+Finsupp.single i 1 := (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)).symm
 have hu : L t + 1= L m:= distill hi
 nth_rw 1 [h]; rw [← comma, call, map_mul, MvPolynomial.aeval_X,←hu,pow_succ]
 apply (free.gain_mul O hO _ _).trans; refine mul_le_mul (straight t) ((u i).trans (by rw [free_stamp,one_mul])) (free.collect _ hO _ ) (by positivity)
termination_by L m
decreasing_by have he:=distill hi; omega
-- binder A missing context `u`
include U hA
theorem senses (m:Letters I): F.gain O (Q (glyph m)) k ≤ (2*M)^L m * F.face A m:= by
 obtain he|he:= eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp he, silent, mul_one]; simp only [show L (0:Letters I)=0 from rfl, show glyph (0: Letters I)=1 from rfl, map_one,pow_zero,Tier.once]; rfl
 obtain ⟨i,hi⟩:= he
 let t:=m-Finsupp.single i 1; have h:m=t+Finsupp.single i 1:= (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)).symm
 have hu : L t + 1= L m:= distill hi
 have H0:= straight hO u hM t -- order inspect
 have H1:= senses t
 let A0:=(2*M)^L t; have h0:0≤A0:= pow_nonneg (by positivity) _;
 have he : M^ L t ≤ A0 := by unfold A0; gcongr; linarith
 let K := A0*M*F.face A m
 nth_rw 1 [h]; rw [← comma, call,map_mul,MvPolynomial.aeval_X,←hu,pow_succ]
 apply (F.twice_all O hO _ _).trans; refine le_trans (b:=K+K) (add_le_add ?_ ?_) (le_of_eq (by unfold K A0; ring));
 · exact (mul_le_mul (H0.trans he) ((U i).trans (mul_le_mul_of_nonneg_right (F.degree A hA m i hi) hM)) (F.collect _ hO _) h0).trans (le_of_eq (by unfold K; ring))
 have hA' := F.bright A hA m
 exact (mul_le_mul (H1.trans (mul_le_mul_of_nonneg_left (F.grows A hA _ m tsub_le_self) h0)) ((u i).trans (by rw [free_stamp, one_mul])) (free.collect _ hO _) (mul_nonneg h0 hA')).trans (le_of_eq (by unfold K; ring))
termination_by L m
decreasing_by have he:=distill hi; omega

lemma marching (P:Packet I)(hP:P.totalDegree≤d) (h:1≤2*M): F.gain O (Q P) k ≤ (2*M)^d* F.valueOf A P:= by
 nth_rw 1 [resolves P]; rw [map_sum]; apply (F.sumUp O hO _ _).trans; rw [capital F _ hA, mul_sum]; apply sum_le_sum; intro m hm
 rw [map_smul,coin_steady];
 have H := (show L m ≤ totalDegree P from MvPolynomial.le_totalDegree hm).trans hP
 exact (mul_le_mul_of_nonneg_left ((senses hO hA U u hM m).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h H) (F.bright _ hA _))) (norm_nonneg _)).trans (le_of_eq (by ring))
lemma thoughts (P:Channel I)(hP:Binary.slim P k d)(h:1≤2*M): F.gain O (replot w P) k≤ (2*M)^d* F.gain A P k:= by
 rw [all_gain]; let x (i:ℕ×ℕ) := F.valueOf O (coeff i.2 (Q (coeff i.1 P)))
 refine le_trans (b:=∑ i∈range (k+1),∑ j∈antidiagonal i,x j) (sum_le_sum (fun i hi=>?_)) (le_trans (triangle_le k x (fun i=>F.lower O hO (coeff i.2 (Q (coeff i.1 P))))) ?_)
 · rw [replot_coeff]; apply many F O hO
 rw [all_gain,mul_sum]; apply sum_le_sum; intro i hi; unfold x; simp_rw [← all_gain]; exact marching hO hA U u hM _ (hP i (Nat.le_of_lt_succ (mem_range.mp hi))) h
end pay

namespace Roads
variable [Fintype J]
variable (T:Tape Y) (p:I→Y)(q:B→Y)(F:Tier) (k n d:ℕ) (w:I→Channel B) (M:ℝ)
local notation "Δ"=> T.Δ

def Along := ∀ i,F.gain (fun j=> Δ (p i) (q j)) (w i) k≤ M
variable (h : Along T p q F k w M)(O:Lens T)
local notation "A"=> O.m ∘ p
local notation "Γ"=> O.m ∘ q
include h O
lemma rich : Targeted F A Γ w k M := by
 intro a; refine (F.gain_alternate Γ _ (fun i=> O.sign (q i)) (w a) (O.sign (p a)) (fun j=>T.sign (p a) (q j)) (fun b=> O.path (q b) (p a))).trans (mul_le_mul_of_nonneg_left (h a) (F.cp (O.sign _)))
omit O in
lemma cashfree : Along T p q free k w M:= fun i=> (Tier.gain_moment free _ (fun j=> T.sign (p i) (q j)) _ (G:=F) (fun x hx => by rw [free_stamp]; exact F.grade hx)).trans (h i)
end Roads

open Roads
variable {p:I→Y} {q:B→Y} (O:Lens T) {F:Tier} {k n d:ℕ} [Fintype I] [DecidableEq I] [Fintype J]
variable {e:Episode I B J}
variable {M:ℝ}
local notation "P"=> Sum.elim p q
local notation "F₀" => Rails e.joint e.vertices k P T F M
variable (H₀:Rails e.joint e.vertices k (Sum.elim p q) T F M) (H: e.Eligible k)
variable (hw:Along T p (Sum.elim p q) F k e.spur M) (h : 2≤M) (hr: (k+1:ℝ)≤M) (hd : (d+3*k:ℝ)≤M)
def expansive (d k:ℕ):= 1+8*(d+3*k)
include H₀ H hw h hr hd in
theorem rough (R : Channel I)(hR : Guard R k d) : F.gain (O.m ∘ q) (e.floats R) k ≤ M^expansive d k * F.gain (O.m ∘ p) R k:= by
 have ht : 1 ≤ M:= by linarith
 have hu : 0≤M:= zero_le_one.trans ht
 have ho : 0≤O.m ∘ p := fun x=> O.sign _; have hp : 0≤O.m ∘ P := fun x=> O.sign _; have hF:= F.collect _ ho R (k:=k)
 have hs := easy O H.rank e.law H₀ h hr hd _ (Guard.prep hR _ H.spur); apply hs.trans
 refine (mul_le_mul_of_nonneg_left (thoughts hp ho (rich T p _ _ k _ M hw O) (rich T p _ _ _ _ _ (cashfree T p _ _ _ _ _ hw) O) hu R hR.slim (by linarith)) (by positivity)).trans ?_
 calc
   _ ≤ (M * M^(6*(d+3*k)))*((M^2)^(d+3*k)* F.gain (O.m ∘ p) R k) := by gcongr; nlinarith
   _ = _ := by rw [← pow_mul]; unfold expansive; rw [show 8*(d+3*k)=6*(d+3*k)+2*(d+3*k) by omega, pow_add,pow_add]; ring
end YM.FormalOPE.RG10.HStein
