import YM.FormalOPE.RG10.HStein.Fines
/-! # Single step rough transfer cap at high order and every finite moment tier

Proof by Stein reduction over the *normalized* conditional series. Inherited
 marks don't require invariance here. Allows exponential widths at input
 provided on the SAME block currency; coarse weights use same unit and Tier.age
 (wire routes from one of the marked arguments). Fixed powers. All ranks ≤ given budget.
-/
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

variable (U: readyNow q V O p d r C F) (U₀ : readyNow q V O p d r C free) (hV : Guard V r 0) (hV' : coeff 0 V=0)
variable [Fintype I] [DecidableEq I]
variable (B₀:Rails q V r p T F C) (hc : 2≤C) (hr:(3*(r:ℕ):ℝ)≤C) (hd:(d:ℝ) ≤ C) (hk:k ≤ r)
local notation "Bf"=> C^(6*d)
lemma bonus (hc: 2 ≤ C): 2 * C ^5 ≤ C^6 := by have he:0≤C^5 := pow_nonneg (by linarith) _; rw [pow_succ _ 5,mul_comm]; exact mul_le_mul_of_nonneg_left hc he
include hc in
omit [Fintype I] [DecidableEq I] in
lemma holus : F.valueOf Γ (opt q V k (glyph 0)) ≤ Bf*F.face A 0:= by
 rw [show glyph (0:Z)=(1:P) from rfl,silent,mul_one]
 obtain rfl|hh:= eq_or_ne k 0
 · rw [opt_zero_pay,Tier.unit]; exact one_le_pow₀ (by linarith)
 rw [opt_one_pay _ _ _ hh, Tier.zero]; exact pow_nonneg (by linarith) _ -- inspect

include U U₀ hV hV' B₀ hc hr hd in
lemma pace : readyNow q V O p (d+1) r C F:= by
 intro k hk m hm
 obtain he|he := eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp he]; exact holus O hc
 obtain ⟨y,hy⟩:= he
 let u := m-Finsupp.single y 1
 have hv : m=Finsupp.single y 1+u:= Eq.symm ((add_comm _ u).trans <| Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hy))
 have hh : length u+3*k≤d:= by have h:= distill hy; change length u+1=length m at h; omega
 let K:= Bf* F.face A m
 have ht:1 ≤ C := by linarith
 have h0:0≤ C:= zero_le_one.trans ht
 have hl:= bright F A (nnews O p) m
 have hK:0≤ K:= mul_nonneg (pow_nonneg h0 _) hl;
 nth_rw 1 [hv,← comma];
 suffices he: F.valueOf Γ (opt q V k (glyph (Finsupp.single y 1)*glyph u)) ≤ 2*(C^5*K) by
   apply he.trans; rw [Nat.mul_add,Nat.mul_one,pow_add];
   rw [←mul_assoc 2, mul_comm Bf]; exact (mul_le_mul_of_nonneg_right (bonus hc) hK).trans (le_of_eq (Eq.symm (mul_assoc ..))) -- direction?
 cases y with
 | inl a=>
   let B:= C^5*K
   rw [call,upgrade q V k _ a hV']; apply (plus F Γ (nout O p) _ _).trans
   rw [two_mul]; apply add_le_add
   · refine (early O U B₀ ht hd hk _ hh a).trans ?_; rw [← hv, ←sq]; apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (by norm_num)) hK
   apply (many F Γ (nout O p) _ _).trans; calc
    _ ≤ ∑ _ ∈ antidiagonal k, C*C*C*K:=sum_le_sum (fun i hi=> (release O U hV B₀ ht hr hk _ hh a _ _ (mem_antidiagonal.mp hi)).trans_eq (by rw [← hv]))
    _ ≤ C^2*(C*C*C*K):= by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ _=>C*C*C*K), sum_const, nsmul_eq_mul,card_range];
      have hj: (↑k:ℝ) ≤ r:= by exact_mod_cast hk;
      apply mul_le_mul_of_nonneg_right ?_ (by positivity); push_cast; nlinarith
    _ = _ := by ring
 | inr b=>
   rw [call, upstairs]; apply (twice F Γ (nout O p) _ _).trans
   have H : u ≤ m:= tsub_le_self
   have hp : F.value (A (.inr b)) ≤ F.face A m := F.degree A (nnews O p) m _ hy
   have hl (FZ:Tier) : FZ.valueOf Γ (X b)=FZ.value (A (.inr b)):= by rw [← call,glyph,money FZ _ (nout O p), norm_one, mul_one,level]; rfl
   have hx := le_mul_of_one_le_left hK (one_le_pow₀ (n:=5) ht) -- one argument binder?
   rw [two_mul, hl free, free_stamp, one_mul, hl F]
   apply add_le_add _ ((mul_le_mul hp ((U₀ _ hk u hh).trans_eq (by rw [flat,mul_one])) (Tier.lower free Γ (nout O p) _) (bright F A (nnews O p) m)).trans (le_trans (by rw [mul_comm]) hx))
   exact ((U k hk u hh).trans (mul_le_mul_of_nonneg_left (grows F _ (nnews O p) _ _ H) (pow_nonneg h0 _))).trans hx
include hV hV' B₀ hc hr hd in
/-- One finite mesh, same O.p on both. -/
theorem priced : readyNow q V O p d r C F:= by
 induction d generalizing F with
 | zero=>
   intro k hk m hm; have hh: m=0:= by
                         ext a; have h:=fewer (i:=a) m; simpa using (show m a = 0 by omega)
   subst m; exact holus O hc
 | succ d ih=>
   push_cast at hd; have hb: (d:ℝ) ≤ C:= by linarith
   exact pace O (ih B₀ hb) (ih B₀.noFare hb) hV hV' B₀ hc hr hb
end YM.FormalOPE.RG10.HStein
