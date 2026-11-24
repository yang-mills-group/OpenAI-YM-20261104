import YM.Integration.WilsonPhysicalHistoryInverse

/-! The manuscript's fixed *physical* comparison reference is coarser
than capture. Its true linear inverse is the unrestricted measured
label chart on one finite campaign. For every small exponent a finite
prefix above an admitted reference has a fixed initial cost. Thus the
reference can be kept fixed while that exponent goes to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedFactoryReturn
open Filter Real Finset Lattice Wilson RG RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open Source Labels PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph Work.G08
open scoped Classical Topology BigOperators
variable {G : Gauge}

private theorem tail (R : Run G) (d : ℕ) {γ : ℝ} {cut : ℕ}
    (gates : ∀ i ≥ cut, ∀ p N, i<N →
      (Opened R.family d i p ∧ Opened R.family d (i+1) p) ∧ Gate R.family d N p i γ 1)
    (N n j t : ℕ) (start : cut ≤ j) (jt : j ≤ t) (tN : t ≤ N) (w : R.family.label d) :
    mCost R.family d N n t w ≤ exp (γ*(R.family.S.scale t-R.family.S.scale j)) *
      mCost R.family d N n j w := by
  let X := fun i => mCost R.family d N n i w
  have walk (b : ℕ) (jb : j ≤ b) : b ≤ N → X b ≤ exp (γ*(R.family.S.scale b-R.family.S.scale j))*X j := by
    induction b,jb using Nat.le_induction with
    | base => intro live; simp
    | succ b jb old =>
      intro live
      have hpre := old (Nat.le_trans (Nat.le_succ b) live)
      have gain := (gates b (start.trans jb) n N live).2.1 w
      have fb : 0<factor R.family b := zero_lt_one.trans (factor_positive R.family b)
      have id : (factor R.family b)^γ * exp (γ*(R.family.S.scale b-R.family.S.scale j)) = exp (γ*(R.family.S.scale (b+1)-R.family.S.scale j)) := by
        rw [Real.rpow_def_of_pos fb,←exp_add,R.family.S.scale_succ]
        congr 1
        change log ((R.family.S.block b).val:ℝ)*γ + γ*(_-_) = _
        ring
      calc
        X (b+1) ≤ (factor R.family b)^γ * X b := gain
        _ ≤ (factor R.family b)^γ * (exp (γ*(R.family.S.scale b-R.family.S.scale j))*X j) :=
          mul_le_mul_of_nonneg_left hpre (rpow_pos_of_pos fb _).le
        _ = _ := by rw [←mul_assoc,id]
  exact walk t jt tN

private def headBudget (R : Run G) (t : ℕ) :=
  1 + ∑ i ∈ range t, max 0 (4*stock R.family (i+1))

private theorem prefix_one (R : Run G) (t : ℕ) : 1 ≤ headBudget R t :=
  le_add_of_nonneg_right (sum_nonneg fun _ _ => le_max_left ..)

private theorem prefix_pays (R : Run G) {i t : ℕ} (it : i<t) :
    4*stock R.family (i+1) ≤ headBudget R t := by
  have single := Finset.single_le_sum
    (f:=fun j : ℕ => max 0 (4*stock R.family (j+1))) (fun _ _ => le_max_left ..)
    (Finset.mem_range.mpr it)
  exact (le_max_right _ _).trans (single.trans (le_add_of_nonneg_left zero_le_one))

private theorem finite (R : Run G) (d : ℕ) {U t : ℕ}
    (opens : ∀ j ≥ U, ∀ p, Opened R.family d j p)
    (N n u b : ℕ) (start : U ≤ u) (ub : u ≤ b) (bt : b ≤ t) (bN : b ≤ N)
    (w : R.family.label d) :
    mCost R.family d N n b w ≤ headBudget R t ^ t * mCost R.family d N n u w := by
  let M := headBudget R t
  have M1 : 1 ≤ M := prefix_one R t
  let X := fun j => mCost R.family d N n j w
  have X0 (j : ℕ) : 0 ≤ X j := size_nonneg _ _
  have step (j : ℕ) (uj : u ≤ j) : j ≤ t → j ≤ N → X j ≤ M^j * X u := by
    induction j,uj using Nat.le_induction with
    | base => intro _ _; exact le_mul_of_one_le_left (X0 u) (one_le_pow₀ M1)
    | succ j uj old =>
      intro jt jN
      have g := transfer_cost d N n j R.makes jN (opens j (start.trans uj) n)
        (opens (j+1) (start.trans (uj.trans (Nat.le_succ j))) n) w
      change X (j+1) ≤ 4*stock R.family (j+1)*X j at g
      have h := old (Nat.le_trans (Nat.le_succ j) jt) (Nat.le_trans (Nat.le_succ j) jN)
      calc
        X (j+1) ≤ 4*stock R.family (j+1)*X j := g
        _ ≤ M*X j := mul_le_mul_of_nonneg_right (prefix_pays R jt) (X0 j)
        _ ≤ M*(M^j*X u) := mul_le_mul_of_nonneg_left h (zero_le_one.trans M1)
        _ = _ := by rw [pow_succ]; ring
  exact (step b ub bt bN).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ M1 bt) (X0 u))

/-- Initial admission is independent of γ. For *every* later choice of
γ one fixed scalar M works uniformly over all later cutoff periods,
capture endpoints, and true bare labels, even if the physical reference
u remains fixed. There is no O(Λ) restriction on the length from u to b. -/
theorem coordinates (R : Run G) (hG : G.Simple) (d : ℕ) :
    ∃ U : ℕ, (∀ u ≥ U, ∀ p, Opened R.family d u p) ∧ ∀ γ > 0, ∃ M : ℝ, 1 ≤ M ∧
      ∀ u ≥ U, ∀ N n b, u ≤ b → b ≤ N → ∀ w : R.family.label d,
        mCost R.family d N n b w ≤ M*(exp (γ*(R.family.S.scale b-R.family.S.scale u))*
          mCost R.family d N n u w) := by
  obtain ⟨U,opens⟩ := Filter.eventually_atTop.mp (open_late R.family hG d)
  refine ⟨U,opens,?_⟩
  intro γ γ0
  obtain ⟨t,gates⟩ := Filter.eventually_atTop.mp (ActualOneMarkGraphStep.gates R hG d γ0 zero_lt_one)
  let M := headBudget R t ^ t
  have M1 : 1 ≤ M := one_le_pow₀ (prefix_one R t)
  refine ⟨M,M1,?_⟩
  intro u Uu N n b ub bN w
  let X := fun j => mCost R.family d N n j w
  let E := fun i j => exp (γ*(R.family.S.scale i-R.family.S.scale j))
  have X0 (j) : 0 ≤ X j := size_nonneg _ _
  have E0 (i j) : 0 ≤ E i j := (exp_pos _).le
  have E1 : 1 ≤ E b u := Real.one_le_exp (mul_nonneg γ0.le
    (sub_nonneg.mpr ((OPE.scale_mono R.family.S).monotone ub)))
  change X b ≤ M*(E b u*X u)
  by_cases after : t ≤ u
  · exact (tail R d (gates t le_rfl) N n u b after ub bN w).trans
      (le_mul_of_one_le_left (mul_nonneg (E0 b u) (X0 u)) M1)
  by_cases before : b ≤ t
  · exact (finite R d opens N n u b Uu ub before bN w).trans
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (X0 u) E1) (zero_le_one.trans M1))
  have ut : u ≤ t := by omega
  have tb : t ≤ b := by omega
  have front := finite R d opens N n u t Uu ut le_rfl (tb.trans bN) w
  have back := tail R d (gates t le_rfl) N n t b le_rfl tb bN w
  have age : E b t ≤ E b u := exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (sub_le_sub_left ((OPE.scale_mono R.family.S).monotone ut) _) γ0.le)
  calc
    X b ≤ E b t * X t := back
    _ ≤ E b u * (M*X u) := mul_le_mul age front (X0 t) (E0 b u)
    _ = M*(E b u*X u) := by ring

end YM.Integration.WilsonCapturedFactoryReturn
end
