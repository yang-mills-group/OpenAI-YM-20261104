import YM.GradedFar.Growth.Scenery

/-! # Recover component prices in the step-comparison's scale, and for composing steps -/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d : ℕ} {I J : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
open MS.Book.Program
section cost
variable (Q : Board I)
lemma product_price {v w : ℝ} {p q : ℕ}
    {E F J : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup J]
    {f : I→E} {h : I→F} {z : I→J} (hf : Bill Q p v f) (hh : Bill Q q w h) (he : ∀ᶠ i in Q.l, ‖z i‖ ≤ ‖f i‖*‖h i‖) :
    Bill Q (p+q) (v+w) z := by
  obtain ⟨C,hC,k,hx⟩:=hf; obtain ⟨D,hD,d,hy⟩:=hh
  refine ⟨C*D,mul_pos hC hD,k+d,?_⟩; filter_upwards [hx,hy,he] with i hx hy he
  apply (he.trans (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))).trans_eq
  unfold post; rw [pow_add,neg_add,add_mul,exp_add,pow_add]; ring
lemma product_scalar {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {v w : ℝ} {p q : ℕ} {x : I→E}{f : I→ℂ}
    (hx : Bill Q p v f) (hy : Bill Q q w x) : Bill Q (p+q) (v+w) (fun i=> f i • x i) :=
  product_price Q hx hy (Eventually.of_forall fun _=>le_of_eq (norm_smul ..))
lemma product_fe {E : Type} [NormedRing E] {x y : I→E} {p q : ℕ}{v w : ℝ}
    (hx : Bill Q p v x) (hy : Bill Q q w y) : Bill Q (p+q) (v+w) (fun i=> x i*y i) :=
  product_price Q hx hy (Eventually.of_forall fun _=>norm_mul_le ..)
lemma no_cost {E : Type} [NormedAddCommGroup E] (z : E) : Bill Q 0 0 (fun (_:I)=>z) := Bill.of_bounded Q ‖z‖ (Eventually.of_forall fun _ => le_rfl)
end cost

private lemma between_price {b : Loft G I} {z : I → ℝ} {V : ℝ→ℂ}
    (simple : G.Simple) (h : b.Mid z) (hv : Rhythm V) : Bill (b.board simple) 0 0 (fun i=> V (z i)) := by
  obtain ⟨p,rfl⟩:= Rhythm.from_poly.mp hv
  clear hv
  induction p using Polynomial.induction_on' with
  | add p r hp hr=>simp_rw [Polynomial.eval_add]; exact hp.plus hr
  | monomial i c=>
    have bill : Bill (b.board simple) 0 0 (fun i=> (z i:ℂ)) := by
      refine ⟨1,zero_lt_one,1,?_⟩; filter_upwards [h] with i hi
      rw [pow_zero,one_mul,one_mul,post,pow_one,neg_zero,zero_mul,exp_zero,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hi.1]; exact hi.2.trans (le_add_of_nonneg_left zero_le_one)
    have he k : Bill (b.board simple) 0 0 (fun i=> (z i:ℂ)^k) := by
      induction k with
      | zero=>simpa using no_cost (b.board simple) (1:ℂ)
      | succ k ih=> simp_rw [pow_succ]; simpa using Bill.times ih bill
    simp_rw [Polynomial.eval_monomial]; simpa using Bill.times (no_cost (b.board simple) c) (he i)

def piece (G : Gauge) (d : ℕ) (i j : Toon G d) : Maps G d :=
  chairs G d ((coord j).smulRight (theory i))
lemma stands (A : Module.End ℂ (Sec G d)) : chairs G d A = ∑ i : Toon G d, ∑ j : Toon G d,
    coord i (A (theory j)) • piece G d i j := by
  unfold piece; simp_rw [← _root_.map_smul, ← map_sum]
  apply congr_arg
  ext1 x; nth_rw 1 [← reconstructed x]; rw [map_sum]
  simp_rw [_root_.map_smul,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.smulRight_apply,smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=> ?_; nth_rw 1 [← reconstructed (A (theory i))]; rw [Finset.smul_sum]; simp_rw [smul_smul]; apply Finset.sum_congr rfl; intro j hj; congr 1; ring
lemma engine_cost (Q : Loft G I) (simple : G.Simple) {z : I → ℝ} (h : Q.Mid z) : Bill (Q.board simple) 0 (-(d:ℝ)) (fun i=>engine G d (z i)) := by
  refine ⟨1,zero_lt_one,0,?_⟩; filter_upwards [h] with i hi
  rw [pow_zero,one_mul,one_mul,post,pow_zero,neg_neg,one_mul,exp_nat_mul]
  apply le_trans (engine_pos_bound _ hi.1 d); gcongr; exact hi.2
lemma continuous_rhythm {v : ℝ→ℂ} (hv : Rhythm v) : Continuous v := by
  obtain ⟨p,rfl⟩:= Rhythm.from_poly.mp hv; exact p.continuous.comp Complex.continuous_ofReal

local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "B"=> GroupS.gaugeN N.scheme N.criterion M ν
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma psi_rhythm (k : ℕ) : Rhythm (fun t : ℝ=>coeff k (ψ (-t))) := by
  simpa only [Polynomial.eval_neg,Polynomial.eval_X] using Rhythm.pre (Rhythm.unit.mpr ((H.dilation ν).check.smooth k)) (-Polynomial.X)
lemma Kcontinuity (k d : ℕ) : Continuous (fun s=>chairs G d (coeff k (Kseries N M d (-s)))) := by
  have he (i j : Toon G d) (s : ℝ) : coord i (coeff k (Kseries N M d (-s)) (theory j))=
      (exp s:ℂ)^i.size*coord i (coeff k (B (-s) d) (theory j)) := by
    rw [Kfactor,Dial_coord,length_power]
  simp_rw [stands,he]
  exact continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> Continuous.smul
    (((Complex.continuous_ofReal.comp Real.continuous_exp).pow _).mul (continuous_rhythm (coeff_polynomial H ..))) continuous_const

variable (Q : Loft G I) {z : I→ℝ}(h : Q.Mid z)
include h
lemma clock_terms (k : ℕ) : Bill (Q.board simple) 0 0 (fun i=>coeff k (ψ (-z i))) := between_price simple h (psi_rhythm N M H k)
lemma gauge_terms (k d : ℕ) : Bill (Q.board simple) 0 0 (fun i=>chairs G d (coeff k (B (-z i) d))) := by
  simp_rw [stands]; refine Bill.sum _ fun i _=> Bill.sum _ fun j _=> ?_
  simpa only [add_zero] using product_scalar _ (between_price simple h (coeff_polynomial H i (theory j) k)) (no_cost _ (piece G d i j))
lemma engine_terms (k d : ℕ) : Bill (Q.board simple) 0 (-(d:ℝ)) (fun i=>chairs G d (coeff k (Kseries N M d (-z i)))) := by
  simp_rw [coeff_K,chairs_mul]; simpa only [add_zero] using product_fe _ (engine_cost Q simple h) (gauge_terms N M H Q h k d)
end
end YM.FVA2.GradedFar.Growth
