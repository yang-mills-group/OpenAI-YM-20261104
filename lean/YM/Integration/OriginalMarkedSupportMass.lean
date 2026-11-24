import YM.Push.GRID_APPROXIMATION.Hit

/-! Pay the actual regular activities reaching a marked set of sites from
their original per-anchor charges, with no factor of the torus volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedSupportMass

open Function Finset Lattice RG Wilson Push.GridApprox.Attach
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

def traversal (p : BudgetPoint) (y x : Site n) : ℝ :=
  Real.exp (-p.supportExponent*((separation y x / leg p.B : ℕ):ℝ))

private theorem shell_scale (B r t : ℕ) : r*(t/leg ((B+1)*r))≤t/leg B := by
  apply (Nat.le_div_iff_mul_le (leg_pos B)).mpr
  calc r*(t/leg ((B+1)*r))*leg B = (t/leg ((B+1)*r))*(r*leg B) := by ring
       _ ≤ (t/leg ((B+1)*r))*leg ((B+1)*r) := Nat.mul_le_mul_left _ (by unfold leg; nlinarith)
       _ ≤ _ := Nat.div_mul_le_self ..

theorem traversal_sum (p : BudgetPoint) (x : Site n) (r : ℕ) (hr : 1≤p.supportExponent*r) :
    ∑ y : Site n,traversal p y x ≤ hitConstant ((p.B+1)*r) := by
  refine le_trans (Finset.sum_le_sum fun y _ => ?_) (all_marks id Function.injective_id x ((p.B+1)*r))
  unfold traversal
  rw [separation_comm y x]
  apply Real.exp_le_exp.mpr
  let k := separation x y/leg ((p.B+1)*r)
  have h : (r:ℝ)*(k:ℝ) ≤ ((separation x y/leg p.B:ℕ):ℝ) := by exact_mod_cast shell_scale p.B r (separation x y)
  have h₁ := mul_le_mul_of_nonneg_right hr (show 0≤(k:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left h p.exponent_pos.le
  change -p.supportExponent*((separation x y/leg p.B:ℕ):ℝ) ≤ -(k:ℝ)
  nlinarith only [h₁,h₂]

variable (A : Activities G n) (p : BudgetPoint) (b : ℕ→ℝ) (hb : ∀ i,0≤b i) {ε : ℝ}
    (roots : ∀ y : Site n, SumBudget
      (fun i => if (A.reg i).site=y then p.mass (A.reg i).support (b i) else 0) ε)

include hb roots

private theorem anchored (x y : Site n) :
    SumBudget (fun i => if (A.reg i).site=y ∧ x∈(A.reg i).support then b i else 0)
      (traversal p y x*ε) := by
  let f (i : ℕ) := if (A.reg i).site=y then p.mass (A.reg i).support (b i) else 0
  let q (i : ℕ) := if (A.reg i).site=y ∧ x∈(A.reg i).support then b i else 0
  have h0 (i : ℕ) : 0≤q i := by unfold q; split <;> first | exact hb i | exact le_rfl
  have ht : 0≤traversal p y x := (Real.exp_pos _).le
  have le (i : ℕ) : q i≤traversal p y x*f i := by
    by_cases hit : (A.reg i).site=y ∧ x∈(A.reg i).support
    · have hy : y∈(A.reg i).support := hit.1 ▸ (A.reg i).anchor
      have cover : ((separation y x/leg p.B:ℕ):ℝ) ≤ coverNumber p.B (A.reg i).support := by
        exact_mod_cast distance_charge (A.reg i).support p.B y x hy hit.2
      simp only [q,f,if_pos hit,if_pos hit.1,traversal,BudgetPoint.mass]
      rw [←mul_assoc,←Real.exp_add]
      apply le_mul_of_one_le_left (hb i)
      apply Real.one_le_exp
      nlinarith only [mul_nonneg p.exponent_pos.le (sub_nonneg.mpr cover)]
    · simp only [q,if_neg hit]
      exact mul_nonneg ht ((roots y).1 i)
  have summ : Summable (fun i => traversal p y x*f i) := (roots y).2.1.mul_left _
  have good := summ.of_nonneg_of_le h0 le
  refine ⟨h0,good,(good.tsum_le_tsum le summ).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (roots y).2.2 ht

theorem site (x : Site n) (r : ℕ) (hr : 1≤p.supportExponent*r) :
    SumBudget (fun i => if x∈(A.reg i).support then b i else 0) (hitConstant ((p.B+1)*r)*ε) := by
  let q i := if x∈(A.reg i).support then b i else 0
  let f (y : Site n) i := if (A.reg i).site=y ∧ x∈(A.reg i).support then b i else 0
  have h0 (i : ℕ) : 0≤q i := by unfold q; split <;> first | exact hb i | exact le_rfl
  have each y := anchored A p b hb roots x y
  have sums (i : ℕ) : ∑ y,f y i=q i := by
    by_cases h : x∈(A.reg i).support <;> simp [q,f,h]
  have hε : 0≤ε := (tsum_nonneg (roots x).1).trans (roots x).2.2
  have cap (t : Finset ℕ) : ∑ i∈t,q i≤hitConstant ((p.B+1)*r)*ε := by
    calc ∑ i∈t,q i = ∑ y,∑ i∈t,f y i := by rw [Finset.sum_comm]; simp_rw [sums]
         _ ≤ ∑ y,traversal p y x*ε := Finset.sum_le_sum fun y _ =>
           ((each y).2.1.sum_le_tsum t (fun i _ => (each y).1 i)).trans (each y).2.2
         _ ≤ _ := by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (traversal_sum p x r hr) hε
  have good := summable_of_sum_le h0 cap
  exact ⟨h0,good,good.tsum_le_of_sum_le cap⟩

theorem carrier (S : Finset (Site n)) (r : ℕ) (hr : 1≤p.supportExponent*r) :
    SumBudget (fun i => if ¬Disjoint (A.reg i).support S then b i else 0)
      (S.card*(hitConstant ((p.B+1)*r)*ε)) := by
  let q i := if ¬Disjoint (A.reg i).support S then b i else 0
  let f (x : Site n) i := if x∈(A.reg i).support then b i else 0
  have h0 (i : ℕ) : 0≤q i := by unfold q; split <;> first | exact hb i | exact le_rfl
  have each x := site A p b hb roots x r hr
  have report (i : ℕ) : q i ≤ ∑ x∈S,f x i := by
    by_cases he : Disjoint (A.reg i).support S
    · rw [show q i=0 from if_neg (fun h => h he)]
      exact Finset.sum_nonneg fun x _ => (each x).1 i
    · obtain ⟨x,hx,hS⟩ := Finset.not_disjoint_iff.mp he
      have z := Finset.single_le_sum (f:=fun x=>f x i) (fun x _ => (each x).1 i) hS
      simpa only [q,f,if_pos he,if_pos hx] using z
  have cap (t : Finset ℕ) : ∑ i∈t,q i≤S.card*(hitConstant ((p.B+1)*r)*ε) := by
    calc ∑ i∈t,q i ≤ ∑ i∈t,∑ x∈S,f x i := Finset.sum_le_sum fun i _ => report i
         _ = ∑ x∈S,∑ i∈t,f x i := Finset.sum_comm
         _ ≤ ∑ _x∈S,hitConstant ((p.B+1)*r)*ε := Finset.sum_le_sum fun x _ =>
           ((each x).2.1.sum_le_tsum t (fun i _ => (each x).1 i)).trans (each x).2.2
         _ = _ := by simp
  have good := summable_of_sum_le h0 cap
  exact ⟨h0,good,good.tsum_le_of_sum_le cap⟩

end YM.Integration.OriginalMarkedSupportMass
