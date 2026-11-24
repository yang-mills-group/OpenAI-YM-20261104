import YM.GradedFar.Growth.Tare
/-!
# Regain the sharp powers asserted in QScale
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=>Teller.logNu 1
local notation "B"=> GroupS.gaugeN N.scheme N.criterion M ν
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Z : Coven G d) (θ : ℝ→ℝ) (ht : Tendsto (fun r=>θ r/gYM G r) τ (𝓝 1)) (hv : travels Z)
  (pc : ∀ p : ℕ, 1≤p → PFrame N M Z θ p) (pt : ∀ p : ℕ,1≤p → PTheta N M θ p)

lemma stripped (x : ℂ) (p d : ℕ) (s : ℝ) :
    engine G d (-s)*crank N M d s p x = blend (names (B (-s) d)) p x := by
  unfold crank blend; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [show engine G d (-s)* (x^i • names (Kseries N M d (-s)) i) = x^i • (engine G d (-s)* names (Kseries N M d (-s)) i) from (by ext1 v; exact map_smul (engine G d (-s)) _ _)]; unfold names; rw [coeff_K,chairs_mul]
  change _ • (engine G d (-s)*(engine G d s*_))=_; rw [← mul_assoc, ← engine_sum, neg_add_cancel, engine_zero, one_mul]

lemma back (r s : ℝ) (h : travels Z) :
    Z (r*exp s) (-s) * Z r s=1 ∧ Z r s * Z (r*exp s) (-s)=1 := by
  rw [← h.2,add_neg_cancel,h.1]
  have he:= h.2 (r*exp s) (-s) s; rw [neg_add_cancel,h.1, mul_assoc, ← exp_add,add_neg_cancel,exp_zero,mul_one] at he
  exact ⟨he.symm,rfl⟩
include H ht hv pt pc
local notation "R"=> RowSpace G d
lemma recovers (Q : Loft G I) (s : I→ℝ) (hs : Q.Mid s) :
    ∀ᶠ i in Q.path, ‖engine G d (-s i) * Z (Q.r i) (s i) - 1‖ ≤ 1/2 := by
  obtain ⟨p,hp⟩:= (for_year N M H Z θ ht hv pc pt Q s hs 1).exists
  let V i:=Z (Q.r i) (s i); let Y i:=crank N M d (s i) p (θ (Q.r i):ℂ); let P i:= engine G d (-s i)
  let f (k : ℕ) i:= (θ (Q.r i):ℂ)^k • names (B (-s i) d) k
  let L:= Q.board simple
  have fe : ∀ k ∈ Finset.Icc 1 p,Bill L 1 0 (f k) := by
    intro i hi
    simpa only [add_zero] using product_scalar _ ((Stock.powers _ _ (start_theta N M H θ ht Q) i).mono_fee le_rfl (Finset.mem_Icc.mp hi).1) (gauge_terms N M H Q hs i d)
  have start : Tendsto (fun i=> P i*Y i-1) Q.path (𝓝 0) := by
    refine (lofty N M H Q (Bill.sum _ fe) (by simp)).congr (fun i=>?_)
    have he : Finset.Icc 1 p=(Finset.range (p+1)).erase 0:= by
      ext; simp; omega
    have hw : ∑ k∈Finset.range (p+1), f k i = P i*Y i := by unfold P Y; rw [stripped]; rfl
    rw [he,←hw,←Finset.add_sum_erase (Finset.range (p+1)) (f:=fun k=> f k i) (Finset.mem_range.mpr (show 0<p+1 by omega)),show f 0 i=1 by unfold f; rw [pow_zero, one_smul,names,(H.dilation ν).check.paid (-s i) d|>.zero,chairs_one]]; abel
  filter_upwards [hp,hs,start.eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1/4)), (Q.board simple).shrinking.eventually_lt_const (show (0:ℝ)<1/4 by norm_num)] with i hi hs he hQ
  rw [pow_one] at hi
  have hw: ‖P i*(V i-Y i)‖≤1/4 := by
    have hk: ‖V i-Y i‖ ≤ 1/4:= ((le_add_of_nonneg_left (show 0 ≤ theta_err N M θ p _ _ from norm_nonneg _)).trans hi).trans hQ.le
    exact (norm_mul_le ..).trans ((mul_le_mul (engine_neg_bound (-s i) (by have := hs.1; linarith) d) hk (norm_nonneg _) zero_le_one).trans_eq (by ring))
  change ‖P i*V i-1‖ ≤ _
  rw [show P i*V i-1=P i*(V i-Y i)+(P i*Y i-1) by rw [mul_sub]; abel]; exact (norm_add_le ..).trans ((add_le_add hw ((mem_ball_zero_iff.mp he).le)).trans_eq (by norm_num)) -- mem_ball
lemma sharp (Q : Loft G I) (s : I→ℝ) (hs : Q.Mid s) : ∀ᶠ i in Q.path,
    ‖Z (Q.r i) (s i)‖ ≤ 2*exp (s i)^d ∧ ‖Z (Q.r i*exp (s i)) (-s i)‖ ≤ 2 := by
    filter_upwards [recovers N M H Z θ ht hv pc pt Q s hs,hs] with i hi h
    let L := engine G d (s i); let E := engine G d (-s i); let V:= Z (Q.r i) (s i); let A:= E*V
    let C:= Z (Q.r i*exp (s i)) (-s i)
    have hk : L*A=V:= by unfold A L E; rw [← mul_assoc, ← engine_sum,add_neg_cancel, engine_zero, one_mul]
    change ‖A-1‖ ≤ 1/2 at hi
    have he (x:R): ‖x‖≤2*‖A x‖ := by
      have hh:= le_trans ((A-1).le_opNorm x) (mul_le_mul_of_nonneg_right hi (norm_nonneg x)); change ‖A x-x‖ ≤ _ at hh
      have ht:=norm_add_le (x-A x) (A x); rw [sub_add_cancel,norm_sub_rev] at ht; linarith only [hh,ht]
    constructor
    · change ‖V‖≤_; rw [←hk]; apply le_trans (norm_mul_le ..)
      have hp:=norm_add_le (A-1) (1 : Maps G d); rw [sub_add_cancel] at hp
      have hw : ‖(1: Maps G d)‖ ≤ 1:= by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; exact le_rfl
      exact (mul_le_mul (engine_pos_bound _ h.1 d) (show ‖A‖≤2 from by linarith only [hw,hp,hi]) (norm_nonneg _) (by positivity)).trans_eq (mul_comm ..)
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num); intro x
    change ‖C x‖ ≤ _
    rw [show C x=C x from rfl]; apply le_trans (he (C x)); gcongr
    change ‖(A*C) x‖ ≤ _; rw [show A*C=E from (by unfold A; rw [mul_assoc,(show V*C=1 from (back Z _ _ hv).2),mul_one])]; exact (E.le_opNorm _).trans ((mul_le_mul_of_nonneg_right (engine_neg_bound _ (neg_nonpos.mpr h.1) d) (norm_nonneg _)).trans_eq (one_mul _))
lemma norms {C b : ℝ} (c0:0<C)(b0:0<b) : ∀ᶠ r in τ, ∀ s≥0, exp s ≤ C*g r^(-b) →
    ‖Z r s‖ ≤ 2*exp s^d ∧ ‖Z (r*exp s) (-s)‖ ≤ 2 := by
  filter_upwards [eventually_comap.mp (sharp N M H Z θ ht hv pc pt _ _ (tree G c0 b0)),positive_g simple] with r hr pr s hs h
  exact hr ⟨(r,s),(intoCourt r C b pr c0 s hs).mpr h⟩ rfl
end
end YM.FVA2.GradedFar.Growth

