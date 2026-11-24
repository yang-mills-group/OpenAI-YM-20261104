import YM.Integration.WilsonPositionPrescribedTariff

/-! The actual coefficient of the independently normalized hierarchy from the
finite polynomial in its source kernel and its simultaneous input changes.
Orders assigned independently to a kernel and to its true input slots are
retained exactly when their sum is the filed coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedAllocations
open Function Finset PowerSeries Maxwell XSpace XSpace.Normalize
open scoped BigOperators Classical
variable {G : Gauge} {d n : ℕ}

abbrev Assign (n q : ℕ) := Option (Fin n) → Fin (q+1)

def total {q : ℕ} (f : Assign n q) := ∑ i, (f i).val

private def file {q : ℕ} (f : Assign n q) : Days n :=
  Finsupp.equivFunOnFinite.symm (fun i=>(f i).val)

private lemma filed {q : ℕ} (f : Assign n q) (i) : file f i=(f i).val := by
  simp [file]

private lemma distinct {q : ℕ} (f g : Assign n q) (h : file f=file g) : f=g := by
  funext i
  apply Fin.ext
  simpa only [filed] using DFunLike.congr_fun h i

def slice (n q e : ℕ) : Finset (Assign n q) := univ.filter (fun f=>total f=e)

/-- The rows at a named affordable order exhaust the *actual* native
allocation, including the zeroth, empty-slot, and all-coincident-order cases. -/
theorem ranks (q e : ℕ) (he : e≤q) (U : Days n→ℂ) :
    ∑ f ∈ slice n q e,U (file f) = ∑ a ∈ tally e n,U a := by
  classical
  apply Finset.sum_bij (fun f _=>file f)
  · intro f hf
    apply (totaled _).mpr
    simpa only [filed,total] using (mem_filter.mp hf).2
  · intro a _ b _ h
    exact distinct a b h
  · intro a ha
    have hsum := (totaled _).mp ha
    have le (i : Option (Fin n)) : a i≤e := hsum ▸ single_le_sum
      (f:=fun j=>a j) (fun j _=> Nat.zero_le (a j)) (mem_univ i)
    let f : Assign n q := fun i=>⟨a i,Nat.lt_succ_of_le ((le i).trans he)⟩
    exact ⟨f,mem_filter.mpr ⟨mem_univ _,hsum⟩,Finsupp.ext (fun i=>filed f i)⟩
  · intro f _
    rfl

/-- The genuinely filed MS kernel/field substitution coefficient, indexed
in the same finite box used by the numerical test. -/
theorem coefficient (q e : ℕ) (he : e≤q) (T : Guard G d) (K : Reports G d)
    (φ : Test n) (v : Fin n → Sec G d) :
    ∑ f ∈ slice n q e,K (f none).val n φ (fun i=>coeff (f (some i)).val T (v i))
      = realm T K e n φ v := by
  rw [really]
  trans ∑ f ∈ slice n q e,K (file f none) n φ (pulseU (file f) T v)
  · apply sum_congr rfl
    intro f _
    rw [filed]
    congr 1
  · exact ranks (n:=n) q e he (fun a=> K (a none) n φ (pulseU a T v))

private def join (n q : ℕ) : (Fin (q+1) × (Fin n→Fin (q+1))) ≃ Assign n q where
  toFun z := fun i=> i.elim z.1 z.2
  invFun f := (f none,fun i=>f (some i))
  left_inv _ := rfl
  right_inv f := by funext i; cases i <;> rfl

def amount {q : ℕ} (T : Guard G d) (K : Reports G d) (φ : Test n) (v : Fin n→Sec G d)
    (f : Assign n q) : ℂ := K (f none).val n φ (fun i=>coeff (f (some i)).val T (v i))

/-- Evaluation of the true finite kernel on the simultaneously changed true slots,
including products whose total degree is higher than the target truncation. -/
theorem rectangle (q : ℕ) (T : Guard G d) (K : Reports G d) (φ : Test n)
    (v : Fin n → Sec G d) (t : ℂ) :
    ∑ k : Fin (q+1),t^k.val *
        K k.val n φ (fun i=>∑ b : Fin (q+1),t^b.val • coeff b.val T (v i)) =
    ∑ f : Assign n q,t^(total f) * amount T K φ v f := by
  classical
  rw [←Equiv.sum_comp (join n q),Fintype.sum_prod_type]
  apply sum_congr rfl
  intro k _
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ,Finset.mul_sum]
  apply sum_congr rfl
  intro b _
  rw [MultilinearMap.map_smul_univ,smul_eq_mul,←mul_assoc]
  change (t^k.val * ∏ i,t^(b i).val) * _ = t^(total (join n q (k,b))) * _
  rw [total,Fintype.sum_option,pow_add,Finset.prod_pow_eq_pow_sum]
  rfl

/-- Actual signed low coefficients; integration will use their original test,
not a separate extraction on each leg. -/
theorem low (q : ℕ) (T : Guard G d) (K : Reports G d) (φ : Test n)
    (v : Fin n → Sec G d) (t : ℂ) :
    ∑ e ∈ range (q+1),t^e * realm T K e n φ v =
    ∑ f : Assign n q,if total f≤q then t^(total f) * amount T K φ v f else 0 := by
  classical
  calc _ = ∑ e ∈ range (q+1), ∑ f : Assign n q,
        if total f=e then t^e * amount T K φ v f else 0 := by
          apply sum_congr rfl
          intro e he
          rw [←coefficient q e (by simpa using he) T K φ v, Finset.mul_sum,slice,Finset.sum_filter]
          rfl
    _ = _ := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro f _
      simp [Finset.sum_ite_eq,Finset.mem_range]

/-- Uniform numerical price for *all* terms above the filed total order.
It uses the entering kernel and the actual field changes, before the test is
averaged or its signed diagnostic applied. -/
theorem miss (q : ℕ) (T : Guard G d) (K : Reports G d) (φ : Test n) (v : Fin n→Sec G d) :
    ∃ C : ℝ,0≤C ∧ ∀ t : ℝ, |t|≤1 →
      ‖(∑ k : Fin (q+1),(t:ℂ)^k.val *
          K k.val n φ (fun i=>∑ b : Fin (q+1),(t:ℂ)^b.val • coeff b.val T (v i))) -
        ∑ e ∈ range (q+1),(t:ℂ)^e * realm T K e n φ v‖ ≤ C * |t|^(q+1) := by
  classical
  refine ⟨∑ f : Assign n q,‖amount T K φ v f‖,Finset.sum_nonneg (fun _ _=>norm_nonneg _),?_⟩
  intro t ht
  rw [rectangle,low,←Finset.sum_sub_distrib,Finset.sum_mul]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro f _
  by_cases h : total f≤q
  · simp only [if_pos h,sub_self,norm_zero]
    positivity
  · simp only [if_neg h,sub_zero,norm_mul,norm_pow, Complex.norm_real,Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg t) ht (by omega)) (norm_nonneg _)

end YM.Integration.WilsonPositionPrescribedAllocations

