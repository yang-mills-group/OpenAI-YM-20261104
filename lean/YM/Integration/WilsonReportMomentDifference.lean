import YM.Comparison.RG02.Cumulants.Partition
import YM.OPE.Therm.Law

/-! Connected correlations of the actual finite Wilson law and of the proposed
report representatives on the same normalized coarse scene. The moment estimates
are required on every subset. Disconnected products are formed only after the
corresponding subset has been integrated in its own common marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportMomentDifference
open Finset Filter MeasureTheory Lattice Wilson RG Source Marker Multi Primitives.GCC.Anchor
open Comparison.RG02.Cumulants OPE
open Extra.Trajectories (connected)
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] (Γ : Census V)
variable {G : Gauge} (C : Family G) {N p k : ℕ}

def microscopic (F : V → Config G (C.side N p) → ℂ) : Poly Γ :=
  Poly.inject fun s => moment (C.beta N p) (fun U => ∏ j ∈ s.val, F j U)

def reported (S : V → Config G (C.side k p) → ℂ) : Poly Γ :=
  Poly.inject fun s => ∫ U, ∏ j ∈ s.val, S j U ∂(Therm.scene C.path N p k)

def multiplicity (s : Γ.Mode) : ℝ :=
  ∑ t ∈ shards Γ s, ‖mobiusTop t.val.card‖ * (t.val.card : ℝ)

private theorem product_gap {I : Type*} [DecidableEq I] (q : Finset I) (f g : I → ℂ)
    {e M : ℝ} (he : 0 ≤ e) (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ M)
    (h : ∀ i, ‖f i-g i‖ ≤ e) : ‖(∏ j ∈ q, f j) - (∏ j ∈ q, g j)‖ ≤ q.card*e*M^q.card := by
  induction q using Finset.induction_on with
  | empty => simp
  | @insert i q hi ih =>
    let X := ∏ j ∈ q, f j
    let Y := ∏ j ∈ q, g j
    have hy : ‖Y‖ ≤ M^q.card := by
      dsimp only [Y]
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hg j)).trans_eq (by simp)
    simp only [prod_insert hi,card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    change ‖f i*X-g i*Y‖ ≤ ((q.card:ℝ)+1)*e*(M^q.card*M)
    calc
      _ = ‖f i*(X-Y)+(f i-g i)*Y‖ := congrArg norm (by ring)
      _ ≤ ‖f i‖*‖X-Y‖+‖f i-g i‖*‖Y‖ := by simpa only [norm_mul] using norm_add_le (f i*(X-Y)) ((f i-g i)*Y)
      _ ≤ M*(q.card*e*M^q.card)+e*M^q.card := add_le_add
        (mul_le_mul (hf i) ih (norm_nonneg _) (zero_le_one.trans hM))
        (mul_le_mul (h i) hy (norm_nonneg _) he)
      _ ≤ _ := by nlinarith only [le_mul_of_one_le_right (mul_nonneg he (pow_nonneg (zero_le_one.trans hM) q.card)) hM]

/-- The genuine normalized pre-report cumulant in an arbitrary permitted mode,
including compound labels and all disconnected partition terms. The loss depends
only on the fixed census and the honest size of a single report representative. -/
theorem original (hC : C.Makes) (hk : k ≤ N)
    (F : V → Config G (C.side N p) → ℂ) (S : V → Config G (C.side k p) → ℂ)
    {e M : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) (hM : 1 ≤ M)
    (hS : ∀ j U, ‖S j U‖ ≤ M)
    (moments : ∀ q : Finset V, ‖moment (C.beta N p) (fun U => ∏ j ∈ q,F j U) -
      (∫ U, ∏ j ∈ q,S j U ∂(Therm.scene C.path N p k))‖ ≤ e) (s : Γ.Mode) :
    ‖(connected (microscopic Γ C F)).part s - (connected (reported Γ C (N:=N) S)).part s‖ ≤
      multiplicity Γ s * e * (1+M^(Fintype.card V))^(Fintype.card (Hot Γ)) := by
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability hC.wilson hk
  let A := microscopic Γ C F
  let B := reported Γ C (N:=N) S
  let m := 1+M^(Fintype.card V)
  have hm : 1 ≤ m := le_add_of_nonneg_right (pow_nonneg (zero_le_one.trans hM) _)
  have au : A.part Γ.quiet=1 := by change moment _ (fun U => ∏ j ∈ (∅ : Finset V),F j U)=1; simp [moment]
  have bu : B.part Γ.quiet=1 := by change (∫ U, ∏ j ∈ (∅ : Finset V), S j U ∂μ)=1; simp
  have diff (q : Γ.Mode) : ‖A.part q-B.part q‖≤e := moments q.val
  have bounded (q : Γ.Mode) : ‖B.part q‖≤ M^(Fintype.card V) := by
    have point (U : Config G (C.side k p)) : ‖∏ j ∈ q.val,S j U‖ ≤ M^(Fintype.card V) := by
      rw [norm_prod]
      exact ((Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hS j U)).trans_eq (by simp)).trans
        (pow_le_pow_right₀ hM (Finset.card_le_univ q.val))
    exact (norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall point)).trans_eq (by rw [probReal_univ,mul_one])
  have ac (q : Γ.Mode) : ‖A.part q‖ ≤ m := by
    calc
      _ = ‖(A.part q-B.part q)+B.part q‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((diff q).trans he1) (bounded q))
  have bc (q : Γ.Mode) : ‖B.part q‖ ≤ m := (bounded q).trans (le_add_of_nonneg_left zero_le_one)
  change ‖(connected A).part s - (connected B).part s‖≤_
  rw [log_partition A au, log_partition B bu, ← Finset.sum_sub_distrib, multiplicity,
      Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [← mul_sub, norm_mul]
  have h := product_gap t.val (fun i : Hot Γ => A.part i.val) (fun i : Hot Γ => B.part i.val)
    he hm (fun i => ac i.val) (fun i => bc i.val) (fun i => diff i.val)
  have grow := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm (Finset.card_le_univ t.val))
    (mul_nonneg (Nat.cast_nonneg (α:=ℝ) t.val.card) he)
  exact (mul_le_mul_of_nonneg_left (h.trans grow) (norm_nonneg _)).trans_eq (by dsimp only [m]; ring)

end YM.Integration.WilsonReportMomentDifference
end

