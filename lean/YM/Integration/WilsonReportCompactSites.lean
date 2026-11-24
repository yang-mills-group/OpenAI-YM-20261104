import YM.Extraction.Gaps

/-! Uniform separation on the actual torus for every rounded cell of one compact test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCompactSites
open Filter Set Lattice Extraction
open scoped Topology

private theorem absolute (z : ℤ) : |(z : ℝ)| = (z.natAbs : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

private theorem rounded {n : ℕ} (x : Points n) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) (a : Axis) :
    let u := address t x
    t * (((u i a-u j a).natAbs : ℕ) : ℝ) ≤ |x i a-x j a|+2*t ∧
    |x i a-x j a| ≤ t * (((u i a-u j a).natAbs : ℕ) : ℝ)+2*t := by
  let u := address t x
  let f (v : Fin n) : ℝ := t * (u v a : ℝ)
  have h (v : Fin n) : dist (f v) (x v a) ≤ t := coord_grid_bound ht x v a
  have he : dist (f i) (f j) = t * (((u i a-u j a).natAbs : ℕ) : ℝ) := by
    rw [Real.dist_eq, ← absolute, Int.cast_sub, ← abs_of_pos ht, ← abs_mul]
    congr 1
    dsimp [f]
    ring
  have h1 := dist_triangle4 (f i) (x i a) (x j a) (f j)
  have h2 := dist_triangle4 (x i a) (f i) (f j) (x j a)
  rw [he,dist_comm (x j a) (f j)] at h1
  rw [he,dist_comm (x i a) (f i)] at h2
  change _ ≤ _ ∧ _ ≤ _
  rw [← Real.dist_eq]
  constructor <;> linarith only [h1,h2,h i,h j]

/-- The two constants are bought before the mesh, cutoff, period and test.
The same eventual period works for every placement in the compact set. -/
theorem original (S : Schedule) {n : ℕ} {K : Set (Points n)}
    (hK : IsCompact K) (hc : K ⊆ conf n) :
    ∃ c M : ℝ, 0 < c ∧ 0 < M ∧ ∀ {t : ℝ}, 0 < t → 4*t ≤ c → ∀ k : ℕ,
      ∀ᶠ p : ℕ in atTop, ∀ x ∈ K, ∀ i j : Fin n,
        let u := wrap (S.side k p) ∘ address t x
        t * (separation (u i) (u j) : ℝ) ≤ M ∧
          (i ≠ j → c/2 ≤ t * (separation (u i) (u j) : ℝ)) := by
  classical
  obtain ⟨c0,hc0,hrooms⟩ := Gaps.someGrows S hK hc
  obtain ⟨p0,hroom⟩ := hrooms.exists
  obtain ⟨m,hm⟩ := hK.exists_bound_of_continuousOn (f:=fun x : Points n => x)
    continuous_id.continuousOn
  let c := min c0 1
  let M := 2*|m|+2
  have hcpos : 0 < c := lt_min hc0 zero_lt_one
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨c,M,hcpos,hM,?_⟩
  intro t ht hsmall k
  have ht1 : t ≤ 1 := by linarith only [hsmall, min_le_right c0 (1:ℝ)]
  let Q : ℕ := ⌈M/t⌉₊
  filter_upwards [S.period_strict.tendsto_atTop.eventually_ge_atTop (4*Q+1)] with p hperiod
  have hside : 4*Q+1 ≤ (S.side k p).val :=
    hperiod.trans (Nat.le_mul_of_pos_right _ (S.denominator k).pos)
  intro x hx i j
  let u := address t x
  let z := u i - u j
  let y := wrap (S.side k p) (u i) - wrap (S.side k p) (u j)
  have coord (v : Fin n) (a : Axis) : |x v a| ≤ |m| :=
    (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le (x v) a).trans
      ((PiLp.norm_apply_le x v).trans ((hm x hx).trans (le_abs_self _)))
  have hu (a : Axis) : t * ((z a).natAbs : ℝ) ≤ M := by
    have h1 := (rounded x ht i j a).1
    have h2 := abs_sub (x i a) (x j a)
    change t * (((u i a-u j a).natAbs : ℕ) : ℝ) ≤ M
    dsimp [M]
    linarith only [h1,h2,coord i a,coord j a,ht1]
  have hlift : lift y = z := by
    apply lift_eq_iff.mpr
    refine ⟨(map_sub (wrap (S.side k p)) _ _).symm,?_⟩
    intro a
    have h (a : Axis) : ((z a).natAbs : ℝ) ≤ Q :=
      ((le_div_iff₀ ht).2 (by simpa only [mul_comm] using hu a)).trans (Nat.le_ceil _)
    have hz : |z a| ≤ (Q : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h a
    rw [abs_le] at hz
    omega
  change t * (pdist y : ℝ) ≤ M ∧ (i ≠ j → c/2 ≤ t * (pdist y : ℝ))
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup (s:=Finset.univ)
    (f:=fun a : Axis => (lift y a).natAbs) Finset.univ_nonempty
  have hmax : pdist y = (z a).natAbs := by simpa only [pdist,hlift] using ha
  refine ⟨hmax ▸ hu a,?_⟩
  intro hij
  obtain ⟨b,hb⟩ := hroom x hx j i (Ne.symm hij)
  have hg := hb (0 : ℤ)
  have hsep : c0 ≤ |x i b-x j b| := by simpa [Gaps.distances,Real.dist_eq] using hg
  have hlow : (z b).natAbs ≤ pdist y := by simpa only [hlift] using component_le y b
  have hreal : t * ((z b).natAbs : ℝ) ≤ t * (pdist y : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hlow) ht.le
  have hround := (rounded x ht i j b).2
  change |x i b-x j b| ≤ t * ((z b).natAbs : ℝ)+2*t at hround
  linarith only [hreal,hround,hsep,hsmall,min_le_left c0 (1:ℝ)]

end YM.Integration.WilsonReportCompactSites
