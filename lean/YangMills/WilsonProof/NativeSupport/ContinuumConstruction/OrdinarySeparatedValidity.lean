import YangMills.WilsonProof.NativeSupport.MSOrdinaryOPE

set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar.Ordinary.SeparatedValidity

open Filter Set
open scoped BigOperators Classical Topology

private theorem appendInjective {n m : ℕ} {α : Type*}
    {f : Fin n → α} {g : Fin m → α} (hf : Function.Injective f)
    (hg : Function.Injective g) (cross : ∀ i j, f i ≠ g j) :
    Function.Injective (Fin.append f g) := by
  intro i j
  refine Fin.addCases (motive := fun i => Fin.append f g i = Fin.append f g j → i = j) ?_ ?_ i
  · intro i
    refine Fin.addCases (motive := fun j =>
      Fin.append f g (Fin.castAdd m i) = Fin.append f g j → Fin.castAdd m i = j) ?_ ?_ j
    · intro i' eq
      exact congrArg (Fin.castAdd m) (hf (by simpa using eq))
    · intro j' eq
      exact (cross i j' (by simpa using eq)).elim
  · intro j'
    refine Fin.addCases (motive := fun j =>
      Fin.append f g (Fin.natAdd n j') = Fin.append f g j → Fin.natAdd n j' = j) ?_ ?_ j
    · intro i' eq
      exact (cross i' j' (by simpa using eq.symm)).elim
    · intro j'' eq
      exact congrArg (Fin.natAdd n) (hg (by simpa using eq))

/-- The full cluster and its fixed spectators are eventually separated on both
submitted compacts. The finite cross condition is vacuous if either arity is zero. -/
theorem eventuallySeparated {n m : ℕ} (K : Set (Points n)) (hK : IsCompact K)
    (near : K ⊆ separated n) (E : Set (Points m)) (hE : IsCompact E)
    (far : ∀ y ∈ E, WithLp.toLp 2 (Fin.cons (0 : Spacetime) y.ofLp) ∈ separated (m + 1)) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ E,
      WithLp.toLp 2 (Fin.append (Real.exp (-t) • x).ofLp y.ofLp) ∈ separated (n + m) := by
  classical
  by_cases nk : K.Nonempty
  · by_cases ne : E.Nonempty
    · have cross : ∀ᶠ t : ℝ in atTop, ∀ (i : Fin n) (j : Fin m),
          ∀ x ∈ K, ∀ y ∈ E, Real.exp (-t) • x.ofLp i ≠ y.ofLp j := by
        apply Filter.eventually_all.mpr
        intro i
        apply Filter.eventually_all.mpr
        intro j
        obtain ⟨xMax, _, hMax⟩ := hK.exists_isMaxOn nk
          ((PiLp.continuous_apply 2 (fun _ : Fin n => Spacetime) i).norm.continuousOn)
        obtain ⟨yMin, yMem, hMin⟩ := hE.exists_isMinOn ne
          ((PiLp.continuous_apply 2 (fun _ : Fin m => Spacetime) j).norm.continuousOn)
        have separatedMin : Function.Injective (Fin.cons (0 : Spacetime) yMin.ofLp) :=
          far yMin yMem
        have distance : 0 < ‖yMin.ofLp j‖ := by
          apply norm_pos_iff.mpr
          intro z
          apply Fin.succ_ne_zero j
          apply separatedMin
          simpa only [Fin.cons_succ, Fin.cons_zero] using z
        have decay : Tendsto (fun t : ℝ => Real.exp (-t) * ‖xMax.ofLp i‖) atTop (𝓝 0) := by
          simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const ‖xMax.ofLp i‖
        filter_upwards [decay.eventually (Iio_mem_nhds distance)] with t small
        intro x hx y hy equal
        have lower : ‖Real.exp (-t) • x.ofLp i‖ < ‖y.ofLp j‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMax hx) (Real.exp_pos _).le)
            (lt_of_lt_of_le small (hMin hy))
        exact (ne_of_lt lower) (congrArg norm equal)
      filter_upwards [cross] with t hcross
      intro x hx y hy
      have hs : Function.Injective (Fin.cons (0 : Spacetime) y.ofLp) := far y hy
      apply appendInjective
      · intro i j equal
        change Real.exp (-t) • x.ofLp i = Real.exp (-t) • x.ofLp j at equal
        apply near hx
        have divided := congrArg (fun v : Spacetime => (Real.exp (-t))⁻¹ • v) equal
        simpa [smul_smul, Real.exp_ne_zero] using divided
      · intro i j equal
        apply Fin.succ_injective
        apply hs
        simpa only [Fin.cons_succ] using equal
      · exact fun i j => hcross i j x hx y hy
    · simp [Set.not_nonempty_iff_eq_empty.mp ne]
  · simp [Set.not_nonempty_iff_eq_empty.mp nk]

variable {g : GaugeGroup} {B : Maxwell.Reference g} {A C : Correlation B}

/-- The correlation comparison is required only on separated configurations. -/
def Agrees (A C : Correlation B) : Prop :=
  ∀ n k a x, x ∈ separated n → A n k a x = C n k a x

private theorem reverse (equal : Agrees A C) : Agrees C A :=
  fun n k a x hx => (equal n k a x hx).symm

theorem truncationEq (equal : Agrees A C) {n m : ℕ} (p : Price B n)
    (e h k : ℕ) (b : Fin m → Label B) (t : ℝ) (x : Points n) (y : Points m)
    (hy : WithLp.toLp 2 (Fin.cons (0 : Spacetime) y.ofLp) ∈ separated (m + 1)) :
    truncation B A p e h k b t x y = truncation B C p e h k b t x y := by
  unfold truncation
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro j _
  rw [equal (m + 1) (k - j.val) _ _ hy]

private theorem transferPrice (equal : Agrees A C) {n : ℕ} {a : Fin n → Label B}
    {p : Price B n} (price : ExteriorExpansion B A a p) : ExteriorExpansion B C a p := by
  refine ⟨price.grade, price.collision, price.polynomial, price.continuous, price.bound, ?_⟩
  intro K hK hx m b E hE hy h k
  obtain ⟨c, hc, L, estimate⟩ := price.exterior K hK hx m b E hE hy h k
  refine ⟨c, hc, L, ?_⟩
  filter_upwards [estimate, eventuallySeparated K hK hx E hE hy] with t bound joined
  intro x xMem y yMem
  change ‖C (n + m) k (Fin.append a b)
      (WithLp.toLp 2 (Fin.append (Real.exp (-t) • x).ofLp y.ofLp)) -
      truncation B C p (∑ i, (a i).1) h k b t x y‖ ≤ _
  rw [← equal _ k (Fin.append a b) _ (joined x xMem y yMem),
      ← truncationEq equal p _ h k b t x y (hy y yMem)]
  exact bound x xMem y yMem

theorem exteriorIff (equal : Agrees A C) {n : ℕ} (a : Fin n → Label B) (p : Price B n) :
    ExteriorExpansion B A a p ↔ ExteriorExpansion B C a p :=
  ⟨transferPrice equal, transferPrice (reverse equal)⟩

private theorem transferValid (equal : Agrees A C) {O : OPE B} (valid : Valid B A O) :
    Valid B C O := by
  refine ⟨valid.multilinear, valid.sameInputs, valid.collision, ?_⟩
  intro n a homogeneous
  obtain ⟨p, existsPrice, uniquePrice, output⟩ := valid.homogeneousWord n a homogeneous
  exact ⟨p, (exteriorIff equal a p).mp existsPrice,
    fun q hq => uniquePrice q ((exteriorIff equal a q).mpr hq), output⟩

theorem validIff (equal : Agrees A C) (O : OPE B) : Valid B A O ↔ Valid B C O :=
  ⟨transferValid equal, transferValid (reverse equal)⟩

theorem determinedIff (equal : Agrees A C) : Determined B A ↔ Determined B C := by
  constructor
  · rintro ⟨O, valid, unique⟩
    exact ⟨O, (validIff equal O).mp valid, fun U hU => unique U ((validIff equal U).mpr hU)⟩
  · rintro ⟨O, valid, unique⟩
    exact ⟨O, (validIff equal O).mpr valid, fun U hU => unique U ((validIff equal U).mp hU)⟩

end YangMills.MSbar.Ordinary.SeparatedValidity
end

