import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Overtime
import YangMills.WilsonProof.NativeSupport.Commissioned259.Local

/-! # First-line calculation also needs the orderwise unconverted costs paid at ALL T
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {I J : Type*} {n m h : ℕ} {V : Arenas G} {B : ℝ → Frames G} {R : ℝ → PowerSeries ℂ}
    (L : Law V R B) (P : O.Canon.Physical V R B)
variable {T : I→ℝ} {X : Filter I}

-- no compact-T restrictions on the polynomials
lemma pay_log (hT : ∀ᶠ i in X, 1 ≤ T i) : Fare T X (fun _=>1) (fun i=> ((Real.log (T i)):ℂ)) := by
  refine Fare.of_le 1 1 zero_le_one ?_; filter_upwards [hT] with i hi
  rw [one_mul,one_mul,pow_one,Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hi)]; unfold logs; linarith
lemma rhythm_log (hT : ∀ᶠ i in X, 1 ≤ T i) {f : ℝ→ℂ} (hp : Rhythm f) : Fare T X (fun _=>1) (fun i=> f (Real.log (T i))) := by
  obtain ⟨p,rfl⟩ := Rhythm.from_poly.mp hp
  clear hp
  induction p using Polynomial.induction_on' with
  | add p q a b=> simp_rw [Polynomial.eval_add]; exact Fare.add hT a b
  | monomial n p=> simp_rw [Polynomial.eval_monomial]; exact Fare.cover (Fare.constant _) ((pay_log hT).zero_pow n)

section Degree
variable (hT : ∀ᶠ i in X, 1 ≤ T i)

private lemma eval_D (k : ℕ) (s : ℝ) (q : Toon G k) (v : Sec G k) :
    coord q (Level.Dial k s v) = Extent.token s (heft (flash q)) * coord q v := by
  rw [ ← all_sig v, map_sum, map_sum, map_sum]
  simp_rw [ _root_.map_smul, Level.exact₀, _root_.map_smul, pivotδ, smul_eq_mul]
  rw [ Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _=>?_ ; split_ifs with he
  · subst j; rw [mul_left_comm]
  simp

/-- K's actual coordinate formal series in the through-cap basis (with no equal-grade witness
as input). This is the projection to even a potentially different weight; the field which is
transformed will expand in its own through-cap basis. See `same_grade`. -/
def badge (B : ℝ → Frames G) (η : ℝ) (v : Sec G h) (q : Toon G h) :=
  PowerSeries.mk (fun k => coord q (coeff k (conversion B η h) v))

-- At the projected-to grade, no cost for source weight. Nonzero only same grade. Log power applies
-- to projection even of off-grade, hence clean envelope.
include L hT
lemma badge_cost (v : Sec G h) (b : Toon G h) : Tunes T X (fun i => T i ^ heft (flash b)) (fun i => badge B (-Real.log (T i)) v b) := by
  intro k
  have P : Rhythm (fun s=> coord b (coeff k (B (-s) h) v)) := by
    simpa only [Polynomial.eval_neg,Polynomial.eval_X] using
      (L.proper h k v (coord b)).pre (-(Polynomial.X : Polynomial ℝ))
  have H : Fare T X (fun i=> T i ^ (heft (flash b))) (fun i=> Extent.token (-Real.log (T i)) (heft (flash b))) := by
    refine Fare.bare (IsBigO.of_bound' ?_); filter_upwards [hT] with i hi; unfold Extent.token; rw [neg_neg,Real.exp_log (by linarith),← Complex.ofReal_pow,Complex.norm_real]
  simp_rw [badge, coeff_mk, coeff_conversion, eval_D]
  refine (Fare.mul H (rhythm_log hT P)).extend ?_
  exact Eventually.of_forall fun i=> mul_one _
end Degree

variable {W : ℝ} {K : Set (Points n)} {S : Set (Points m)} (hK : IsCompact K)
    (hx : K⊆conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (hW : 1 ≤ W) (hz : clears W K S) (u : Scan G n) (v : Scan G m)
include P hK hx hS hy hW hz

lemma through_full (k : ℕ) : ∃ D : ℝ, 0 < D ∧ ∃ z : ℕ, ∀ T ≥ W, ∀ x∈K, ∀ y∈S,
    ‖coeff k (party (install V) x (T • y) u v)‖ ≤ D * ((T⁻¹)^(totalG v)*(1+Real.log T)^z) := by
  -- recover F.O bounds on all T using only compact extension
  obtain ⟨A,hA,z,H⟩ := rain_price_T (Ffull P u v hK hx hS hy (k+1) 0 k (Nat.lt_succ_self _))
  obtain ⟨B,hB⟩ := eventually_atTop.mp H
  let Q := max W B
  have hQ : 0 < Q := zero_lt_one.trans_le (hW.trans (le_max_left ..))
  let I := ↥(Icc W Q) × ↥K × ↥S
  let F (x : I) := forest x.2.1.val (x.1.val • x.2.2.val)
  have hi : Continuous F := O.Enh.continual (by unfold I; fun_prop) (by unfold I; fun_prop)
  obtain ⟨C,hC⟩ : ∃ C : ℝ, ∀ i:I, ‖coeff k (party (install V) i.2.1.val (i.1.val • i.2.2.val) u v)‖ ≤ C := by
    haveI := isCompact_iff_compactSpace.mp hK; haveI := isCompact_iff_compactSpace.mp hS
    obtain ⟨C,h⟩ := isCompact_univ.exists_bound_of_continuousOn ((P.awake _ (Fin.append u v) k).comp_continuous hi
      (fun i => hz _ i.1.property.1 _ i.2.1.property _ i.2.2.property)).continuousOn
    exact ⟨C,fun i=> h i (mem_univ _)⟩
  let Z := |C| *Q^(totalG v)
  refine ⟨max A Z,lt_max_of_lt_left hA,z,?_⟩
  intro T hT x H y h
  have tpos := zero_lt_one.trans_le (hW.trans hT)
  have L := Real.log_nonneg (hW.trans hT); rcases le_total T Q with t|t
  · calc
    _ ≤ |C| := (hC (⟨T,hT,t⟩, ⟨x,H⟩, ⟨y,h⟩)).trans (le_abs_self _)
    _ = Z*((Q⁻¹)^(totalG v)*1^z) := by unfold Z; rw [one_pow,mul_one, mul_assoc, ←mul_pow,mul_inv_cancel₀ hQ.ne', one_pow,mul_one]
    _ ≤ _ := by gcongr; exact le_max_right ..; linarith
  specialize hB T ((le_max_right ..).trans t) ((⟨x,H⟩, ⟨y,h⟩) : ↥K × ↥S); dsimp only at hB; rw [squeeze_T T tpos] at hB
  exact hB.trans (by rw [mul_assoc]; gcongr; exact le_max_left ..)
lemma whole_full {x : I → Points n} (hu : ∀ᶠ i in X, x i ∈ K) {y : I → Points m} (hv : ∀ᶠ i in X, y i∈S)
    (ht : ∀ᶠ i in X, W ≤ T i) : Tunes T X (fun i => ((T i)⁻¹)^(totalG v))
      (fun i => party (install V) (x i) (T i • y i) u v) := by
  intro k; obtain ⟨D,hD,z,H⟩ := through_full P hK hx hS hy hW hz u v k
  refine Fare.of_le z D hD.le ?_; filter_upwards [ht,hu,hv] with i h e w; exact H _ h _ e _ w
end YM.FVA2.GradedFar259.Comparing
