import YM.MatchingLedger.Books.Report

/-!
# Linear estimator in SD (actual coupling power with nested tests)

Used also for bounding the formal answers: otherwise estimates of ratios at finite volume
may consume a power of that volume. Applies to fixed rank and order, when ALL the indicated
queries work on the same construction. The supply of the error is further work.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books.FPS
open Function Filter Matrix Finset MvPolynomial
open scoped BigOperators Classical
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (V : ℕ → Poly ι)

structure License (V : ℕ → Poly ι) (T : Fountain (V 0)) (M : ℝ) (n : ℕ) : Prop where
  one : 1≤M
  inverse : ∃ B : Matrix ι ι ℝ, B * T.rank=1 ∧ ∀ i, ∑ j, ‖B i j‖≤M
  stipend : ∀ i, ‖T.subsidy i‖≤ M
  pays k (hk:k≤n) i : (slope V i k).totalDegree≤ k+1 ∧ fare (slope V i k)≤ M

def board (n : ℕ)(M : ℝ) := M*(M+ n + M + (n+1:ℝ)* M)
def height (n q l : ℕ) := q*(n+2)+l
def bill (n : ℕ)(M : ℝ)(q l : ℕ) := (board n M)^(height n q l + 1)
lemma board_one (n : ℕ){M : ℝ}(h:1≤M): 1≤board n M := by
  have he : 0<M:= zero_lt_one.trans_le h; unfold board; apply one_le_mul_of_one_le_of_one_le h
  nlinarith only [Nat.cast_nonneg (α:=ℝ) n,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) he.le,h]
lemma base_cost (n : ℕ){M : ℝ}(h:1≤M): M≤board n M := by
  apply le_mul_of_one_le_right (zero_le_one.trans h); have he : 0<M:= zero_lt_one.trans_le h; nlinarith only [Nat.cast_nonneg (α:=ℝ) n,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) he.le,h]

-- W_q either error functional or formal coefficient.
def ley {ι : Type*} (V : ℕ→Poly ι)(i : ι)(W : ℕ→Prediction ι)(p : Poly ι)(g : ℝ)(q : ℕ) :=
  W q (force V i p)+(∑ e∈antidiagonal q,g^e.2 * W e.1 ((slope V i e.2)*p))
structure Stamp {ι : Type*} (V : ℕ→Poly ι)(g M : ℝ)(W : ℕ → Prediction ι)(n : ℕ) : Prop where
  first q (h:q ≤ n) : ‖W q 1‖ ≤ M*g^(q+1)
  equation (q) (m:Token ι) (h : q + heft m + 1 ≤ n) (i:ι) : ‖ley V i W (mark m) g q‖ ≤ M*g^(q+1)

namespace License
variable {V} {T : Fountain (V 0)} {M g:ℝ} {n:ℕ} (L : License V T M n)
    (hg : 0≤g){W : ℕ → Prediction ι} (H : Stamp V g M W n)
include L H hg
lemma stamped_mark (q : ℕ)(m : Token ι)(hv : q + heft m ≤ n) : ‖W q (mark m)‖ ≤ bill n M q (heft m)*g^(q+1):= by
  let K:= height n q (heft m); generalize hx : height n q (heft m) = X' -- X' general no target match?
  induction X' using Nat.strong_induction_on generalizing q m with
  | _ x ih =>
   have hc : 0≤ M:= zero_le_one.trans L.one
   have he0 : 1≤board n M:= board_one n L.one
   by_cases h:m=0
   · subst m; have ht := H.first q (by omega); change ‖W q 1‖ ≤ _; apply ht.trans; unfold bill; exact mul_le_mul_of_nonneg_right ((base_cost n L.one).trans (le_self_pow₀ he0 (by omega))) (pow_nonneg hg _)
   obtain ⟨i,hi⟩ := (Finsupp.support_nonempty_iff.mpr h); let s:=m-Finsupp.single i 1; let p:=mark s
   have he:0<m i:= Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
   have hs: heft s+1=heft m:= heft_diminish m i he
   have hm: p.totalDegree=heft s:=mark_weight s
   let t:=heft s; let f:=T.rank; let z:= (fun j=>W q (X j*p))
   let A:= board n M; let Z : ℕ :=height n q (heft m)
   have hv'(q : ℕ)(v : Poly ι){l:ℕ}(hd:v.totalDegree≤ l)(hy:q+l≤ n)(hp: height n q l < Z):
       ‖W q v‖≤ fare v*(A^Z*g^(q+1)):= by
     apply by_mark _ _ v hd; intro m hm; have hi : height n q (heft m) < Z := by exact lt_of_le_of_lt (Nat.add_le_add_left hm _) hp
     exact (ih _ (hi.trans_eq hx) _ _ (by omega) rfl).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ he0 hi) (pow_nonneg hg _))
   let Y:= A^Z*g^(q+1); have hv₀:0≤Y:=by unfold Y; have hA:0<A:=zero_lt_one.trans_le he0; positivity
   have hh:q+t+1≤n:=by unfold t; omega
   have hk:height n q t <Z:=by unfold Z height; unfold t; omega
   let t':= M+n+ M + (n+1:ℝ)*M; have ht' : 0≤ t':=by unfold t'; positivity
   have Hk(j:ι) : ‖(f *ᵥ z) j‖ ≤ t'*Y:=by
     let D:= g^(q+1); let v:=ley V j W p g q; let d:= W q (pderiv j p)
     let w := T.subsidy j * W q p; let s' : ℕ×ℕ→ℝ:=fun e=>g^e.2 * W e.1 (slope V j e.2*p); let b:=∑ k∈antidiagonal q, s' k
     have hz(s:ℝ)(p:Poly ι): C s*p=s • p := (Algebra.smul_def s p).symm
     have Ht : W q (base V j*p) = w+(f *ᵥ z) j := by rw [base,T.basis_test,add_mul,sum_mul]; simp_rw [mul_assoc (C _) _ p,hz,map_add,map_sum,map_smul]; rfl
     have ht : (f *ᵥ z) j= v+d-w-b := by unfold v ley force; rw [map_sub,Ht]; unfold b d s'; ring
     have hp: ‖v‖ ≤ M*Y:= le_trans (H.equation q s hh j) (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (pow_nonneg hg _) (one_le_pow₀ he0)) hc)
     have hq: ‖d‖ ≤ n*Y:= (hv' _ _ (le_trans (total_pderiv_mark s j) (Nat.sub_le t _)) (by omega) hk).trans (mul_le_mul_of_nonneg_right ((fare_pderiv_mark s j).trans (Nat.cast_le.mpr (by unfold t at *; omega))) hv₀)
     have hw: ‖w‖≤ M*Y:=by unfold w; rw [norm_mul]; exact mul_le_mul (L.stipend j) ((hv' q p hm.le (by omega) hk).trans_eq (congr_arg (·*Y) (fare_mark s)|>.trans (one_mul Y))) (norm_nonneg _) hc
     have hx(e : ℕ×ℕ)(he:e∈antidiagonal q) : ‖s' e‖ ≤ M*Y:=by
       obtain he : e.1 + e.2=q:= mem_antidiagonal.mp he; have hf:= L.pays e.2 (by omega) j
       rcases eq_or_ne e.2 0 with hb|hb
       · simp [s',hb,slope,higher,mul_nonneg hc hv₀]
       let c := slope V j e.2*p
       let l:=t+e.2+1
       have ht:height n e.1 l<Z:=by
         unfold l t Z height; rw [← he, add_mul]; have h0:0<e.2:= by omega
         rw [mul_add e.2]; omega
       have HL:=hv' e.1 c (le_trans (totalDegree_mul ..) (by unfold l t; omega)) (by unfold l; omega) ht
       have hc': fare c≤ M:=(fare_mul ..).trans ((congr_arg (_*·) (fare_mark s)|>.trans (mul_one _)).trans_le hf.2)
       unfold s'; rw [norm_mul,Real.norm_of_nonneg (pow_nonneg hg _)]
       have hA:0≤ A:= zero_le_one.trans he0
       refine (mul_le_mul_of_nonneg_left (HL.trans (mul_le_mul_of_nonneg_right hc' (by positivity))) (pow_nonneg hg _)).trans_eq ?_
       unfold Y; rw [← he]; rw [add_assoc, pow_add]; ring
     rw [ht]; apply (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hp hq)) hw)) ((norm_sum_le ..).trans (Finset.sum_le_sum (g:=fun _=>M*Y) hx))).trans ?_)
     rw [Finset.sum_const,nsmul_eq_mul,Finset.Nat.card_antidiagonal]; unfold t'; push_cast; have hq : (q:ℝ)≤ n:=by exact_mod_cast (show q ≤ n from by omega)
     nlinarith only [mul_le_mul_of_nonneg_right hq (mul_nonneg hc hv₀)]
   obtain ⟨B,hB,hQ⟩:= L.inverse
   have hp:z=B *ᵥ(f *ᵥ z):= by rw [mulVec_mulVec,hB,one_mulVec]
   have hZ : ‖z i‖ ≤ M * (t'*Y):= by
     rw [hp]; calc
       _ ≤ ∑ j:ι, ‖B i j‖ * (t'*Y):= (norm_sum_le ..).trans (sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (Hk j) (norm_nonneg _) |>.trans' (norm_mul_le ..)))
       _ ≤ _:= by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hQ i) (mul_nonneg ht' hv₀)
   rw [← term_remove he]; apply hZ.trans; unfold t'; change _≤ A^(Z+1)*g^(q+1); rw [pow_succ']; exact (by apply le_of_eq; unfold Y A board; ring)
end License
end YM.MatchingLedger.Books.FPS
