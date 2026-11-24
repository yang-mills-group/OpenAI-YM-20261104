import YM.Integration.WilsonCapturedPrimarySmooth
import YM.Extra.SOURCE_HISTORIES.Unit

/-! Localize a single complete signed coordinate test. A large support pays
its own original cover weight, uniformly on each actual torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCollar
open Function Filter Labels Lattice Wilson RG Source Push.Local Extra.Histories
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ
open WilsonCapturedPrimaryReading
open scoped Classical Topology

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

def radius (P : BudgetPoint) (K : ℕ) := K*(4*P.B+2)+2*P.B

def clip (o : Site n) (r : ℕ) (U : Config G n) : Config G n := fun e =>
  if separation e.1 o ≤ r then U e else 1

def kept (q : Coefficient F n) (P : BudgetPoint) (K : ℕ) : Coefficient F n :=
  {q with regular := fun i => if coverNumber P.B (q.support i) < K then q.regular i else 0}

theorem retained {q : Coefficient F n} {P : BudgetPoint} {A : Hol G} {o : Site n}
    {R : Rep G n} (f : q.Format o A R) {i K} (h : coverNumber P.B (q.support i) < K)
    (U : Config G n) : q.regular i (clip o (radius P K) U) = q.regular i U := by
  apply (f.smooth i).sites
  intro l hl _
  apply if_pos
  exact (Corona.extent (q.support i) P.B hl (f.origin i)).trans (by unfold radius; gcongr)

theorem funded {q : Coefficient F n} {A : Hol G} {o : Site n} {R : Rep G n}
    (f : q.Format o A R) {κ s : ℝ} (paid : q.remBound o R κ s) (K : ℕ) :
    (kept q R.p K).Format o A R ∧ (kept q R.p K).remBound o R κ s := by
  constructor
  · refine ⟨?_,f.origin,?_,?_,f.forcing,f.carried,f.invariant,f.supported,f.borel⟩
    · intro i; simp only [kept]; split <;> [exact f.smooth i; exact (regular0 R.p (q.support i) o).1]
    · intro i; simp only [kept]; split <;> [exact f.identity_null i; rfl]
    · intro i hi; simp only [kept]; split <;> [exact f.projects i hi; exact vanishing0 d o A]
  · obtain ⟨a,b,ha,hb,hs,hκ,⟨e,he,hc⟩,hf⟩ := paid
    refine ⟨a,b,ha,hb,hs,hκ,⟨e,he,?_⟩,hf⟩
    intro i
    simp only [kept]
    split
    · exact hc i
    · exact ⟨(hc i).1,fun U hu l hl w =>
        ((regular0 R.p (q.support i) o).2.2 U hu l hl w).trans (hc i).1⟩

private theorem tail {P : BudgetPoint} {X : ℕ → Support n} {e : ℕ → ℝ} {a C : ℝ}
    (hs : SumBudget (fun i => P.mass (X i) (e i)) a) (hC : 0≤C) (he : ∀ i,0≤e i)
    (v : ℕ → ℂ) (hv : ∀ i, ‖v i‖ ≤ C*e i) (K : ℕ) :
    ‖(∑' i, v i) - ∑' i, (if coverNumber P.B (X i) < K then v i else 0)‖ ≤
      C*Real.exp (-(P.supportExponent*K))*a := by
  let Y (i : ℕ) := if coverNumber P.B (X i) < K then v i else 0
  have esum : Summable e := hs.2.1.of_nonneg_of_le he (fun i => P.loMass _ _ (he i))
  have vs : Summable v := Summable.of_norm_bounded (esum.mul_left C) hv
  have ybound i : ‖Y i‖ ≤ C*e i := by
    dsimp only [Y]; split <;> [exact hv i; simpa using mul_nonneg hC (he i)]
  have ys : Summable Y := Summable.of_norm_bounded (esum.mul_left C) ybound
  let D := C*Real.exp (-(P.supportExponent*K))
  have hD : 0≤D := mul_nonneg hC (Real.exp_nonneg _)
  have diff i : ‖v i-Y i‖ ≤ D*P.mass (X i) (e i) := by
    unfold Y; split
    · simp only [sub_self,norm_zero]; exact mul_nonneg hD (hs.1 i)
    · rename_i long
      rw [sub_zero]
      refine (hv i).trans ?_
      unfold D BudgetPoint.mass
      rw [mul_assoc,←mul_assoc (Real.exp _) (Real.exp _) _,← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hC
      apply le_mul_of_one_le_left (he i)
      apply Real.one_le_exp_iff.mpr
      have hlen : (K:ℝ) ≤ coverNumber P.B (X i) := by exact_mod_cast Nat.le_of_not_gt long
      linarith only [mul_le_mul_of_nonneg_left hlen P.exponent_pos.le]
  change ‖(∑' i, v i) - ∑' i, Y i‖ ≤ _
  rw [←vs.tsum_sub ys]
  have budget := sumBudget_mono (sumBudget_mul_left hs hD)
    (fun i => norm_nonneg (v i-Y i)) diff le_rfl
  exact (norm_tsum_le_tsum_norm budget.2.1).trans budget.2.2

variable {A : Hol G} {B : SectionData F} {o : Site n} {R : Rep G n}

theorem values (hb : B.Sound A) {q : Coefficient F n} (f : q.Format o A R)
    {κ s : ℝ} (paid : q.remBound o R κ s) (K : ℕ)
    (stencil : ∀ x ∈ B.footprint o, separation x o ≤ radius R.p K)
    (U : Config G n) (clear : flags R.p.threshold (clip o (radius R.p K) U) = ∅) :
    ‖reading B R o q (clip o (radius R.p K) U) -
      (B.places (F.scaled R.p.threshold⁻¹ q.x) o U + ∑' i, (kept q R.p K).regular i U)‖ ≤
      Real.exp (-(R.p.supportExponent*K))*s := by
  let W := clip o (radius R.p K) U
  have core : B.places (F.scaled R.p.threshold⁻¹ q.x) o W =
      B.places (F.scaled R.p.threshold⁻¹ q.x) o U :=
    B.placed_local o _ W U (fun l h _ => if_pos (stencil l.1 h))
  have row i : (kept q R.p K).regular i U =
      if coverNumber R.p.B (q.support i) < K then q.regular i W else 0 := by
    by_cases h : coverNumber R.p.B (q.support i) < K
    · simpa only [kept,if_pos h] using (retained f h U).symm
    · simp [kept,h]
  change ‖reading B R o q W - _‖ ≤ _
  rw [on_clear hb q clear,core,add_sub_add_left_eq_sub]
  simp_rw [row]
  obtain ⟨a,b,_,hb',hs,_,⟨e,he,hc⟩,_⟩ := paid
  have hW (i : ℕ) : Healthy R.p.threshold (q.support i) W := by
    unfold Healthy; rw [clear]; simp
  have hv i : ‖q.regular i W‖ ≤ 1*e i := by
    simpa only [one_mul,leftDerivs] using (hc i).2 W (hW i) [] (by simp) (by simp)
  have result := tail he zero_le_one (fun i => (hc i).1) (fun i => q.regular i W) hv K
  simp only [one_mul] at result
  exact result.trans (mul_le_mul_of_nonneg_left (by linarith only [hs,hb']) (Real.exp_nonneg _))

private theorem split_probe {q : Coefficient F n} (f : q.Format o A R)
    {κ s : ℝ} (paid : q.remBound o R κ s) (order : d ≤ R.p.order)
    (power : d ≤ R.p.power) (p : Probe G d) :
    runProbe F p (projection F A R.p.threshold o q) =
      runProbe F p q.x + ∑' i, jet A p R.p.threshold o (q.regular i) := by
  have h := ((vector_summable F A f paid order power).hasSum.mapL (runProbe F p)).tsum_eq
  have row i : runProbe F p (vector F A R.p.threshold o (q.regular i)) =
      jet A p R.p.threshold o (q.regular i) := charged F A _ (computed A (f.smooth i) o order) p
  change (∑' i, runProbe F p (vector F A R.p.threshold o (q.regular i))) = _ at h
  simp_rw [row] at h
  rw [projection,map_add,←h]

theorem omitted (hb : B.Sound A) {q : Coefficient F n} {κ s : ℝ}
    (paid : q.remBound o R κ s) (K : ℕ) (U : Config G n) (clear : flags R.p.threshold U=∅) :
    ‖reading B R o q U - reading B R o (kept q R.p K) U‖ ≤ Real.exp (-(R.p.supportExponent*K))*s := by
  rw [on_clear hb q clear,on_clear hb _ clear]
  change ‖(_+_) - (B.places (F.scaled R.p.threshold⁻¹ q.x) o U+_)‖ ≤ _
  rw [add_sub_add_left_eq_sub]
  obtain ⟨a,b,_,hb',hs,_,⟨e,he,hc⟩,_⟩ := paid
  have healthy i : Healthy R.p.threshold (q.support i) U := by unfold Healthy; rw [clear]; simp
  have hv i : ‖q.regular i U‖ ≤ 1*e i := by
    simpa only [one_mul,leftDerivs] using (hc i).2 U (healthy i) [] (by simp) (by simp)
  have h := tail he zero_le_one (fun i => (hc i).1) _ hv K
  have eqn i : (kept q R.p K).regular i U =
      if coverNumber R.p.B (q.support i) < K then q.regular i U else 0 := by
    by_cases h : coverNumber R.p.B (q.support i) < K <;> simp [kept,h]
  simp_rw [eqn]
  simp only [one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith only [hs,hb']) (Real.exp_nonneg _))

/-- Localization of the original dimensionless field coordinate, for every
probe on the actual finite dual and every native finite Wilson rep. -/
theorem coordinate {q : Coefficient F n} (f : q.Format o A R)
    {κ s : ℝ} (paid : q.remBound o R κ s) (order : d ≤ R.p.order)
    (power : d ≤ R.p.power) (K : ℕ) (p : Probe G d) :
    ‖runProbe F p (projection F A R.p.threshold o q) -
      runProbe F p (projection F A R.p.threshold o (kept q R.p K))‖ ≤
      (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose *
      Real.exp (-(R.p.supportExponent*K))*s := by
  obtain ⟨kf,kp⟩ := funded f paid K
  rw [split_probe f paid order power,split_probe kf kp order power]
  let C := (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose
  have hc : 0≤C := (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose_spec.1
  change ‖(_+_) - (runProbe F p q.x+_)‖ ≤ _
  rw [add_sub_add_left_eq_sub]
  have split i : jet A p R.p.threshold o ((kept q R.p K).regular i) =
      if coverNumber R.p.B (q.support i) < K then jet A p R.p.threshold o (q.regular i) else 0 := by
    by_cases h : coverNumber R.p.B (q.support i) < K
    · simp [kept,h]
    · simp [kept,h,jet,Function.comp_def]
  simp_rw [split]
  obtain ⟨a,b,_,hb,hs,_,⟨e,he,h⟩,_⟩ := paid
  have hv i : ‖jet A p R.p.threshold o (q.regular i)‖ ≤ C * e i :=
    (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose_spec.2
      n o (q.support i) R.p (q.regular i) (e i) order power (f.smooth i) (h i)
  exact (tail he hc (fun i => (h i).1) _ hv K).trans
    (mul_le_mul_of_nonneg_left (by linarith only [hs,hb]) (mul_nonneg hc (Real.exp_nonneg _)))

def cutoff (P : BudgetPoint) (g : ℝ) (T : ℕ) :=
  Nat.ceil (-Real.log (g^T)/P.supportExponent)

theorem cut_price (P : BudgetPoint) {g : ℝ} (hg : 0 < g) (T : ℕ) :
    Real.exp (-(P.supportExponent*cutoff P g T)) ≤ g^T := by
  have h : -Real.log (g^T) ≤ (cutoff P g T:ℝ) * P.supportExponent := (div_le_iff₀ P.exponent_pos).mp
    (Nat.le_ceil (-Real.log (g^T)/P.supportExponent))
  calc
    _ ≤ Real.exp (Real.log (g^T)) := Real.exp_le_exp.mpr (by linarith only [h])
    _ = _ := Real.exp_log (pow_pos hg T)

end YM.Integration.WilsonCapturedPrimaryCollar
