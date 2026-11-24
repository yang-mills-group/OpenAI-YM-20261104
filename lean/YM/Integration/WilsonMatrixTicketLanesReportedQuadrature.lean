import YM.Integration.WilsonMatrixTicketLanesReportedFees
import YM.XSpace.Stairs

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedQuadrature
open Filter Function Set Metric MeasureTheory OPE Lattice XSpace PhysicalNext.Repeat.Legato
open RGComparison.Core16.Astage WilsonMatrixTicketLanesReportedFees
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G) {n : ℕ}

/-- The original finite torus, expressed in the units of the prescribed physical separation. -/
def mesh (m p : ℕ) (r : ℝ) (hr : 0 < r) : Mesh where
  p := { side := R.family.side m p
         even := dvd_trans (by norm_num : 2 ∣ 4) (R.family.S.side_four m p)
         large := Nat.le_of_dvd (R.family.side m p).pos (R.family.S.side_four m p) }
  spacing := R.family.S.a m / r
  positive := div_pos (R.family.S.a_pos m) hr

/-- Each discrete coefficient is the original sample weight, including the full four-dimensional cell volumes. -/
def weight (T : Mesh) (φ : Test n) (c : Four ℝ) (x : T.Tuple (n:=n)) : ℂ :=
  (T.spacing : ℂ)^(4*n) * φ (T.rel (T.back x) c)

theorem mass (φ : Test n) : ∃ B : ℝ, 0 ≤ B ∧ ∀ T : Mesh, T.spacing ≤ 1 → ∀ c : Four ℝ,
    ∑ x : T.Tuple (n:=n), ‖weight T φ c x‖ ≤ B := by
  obtain ⟨b,hb⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have bpos : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  obtain ⟨V,region⟩ := φ.hasCompactSupport.isBounded.subset_closedBall (0 : Points n)
  let U := closedBall (0 : Points n) (V+4*n)
  refine ⟨b * volume.real U, mul_nonneg bpos measureReal_nonneg, ?_⟩
  intro T small c
  let f (x : T.Tuple (n:=n)) : ℂ := ‖φ (T.rel (T.back x) c)‖
  have control (z : Points n) : ‖T.levels c f z‖ ≤ b ∧ (z ∉ U → T.levels c f z = 0) := by
    by_cases occupied : ∃ x : T.Tuple (n:=n), z ∈ T.cell c (T.back x)
    · obtain ⟨x,here⟩ := occupied
      rw [T.stair_at c z here]
      refine ⟨by simpa [f] using hb (T.rel (T.back x) c),?_⟩
      intro out
      by_cases inside : T.rel (T.back x) c ∈ tsupport φ
      · exfalso
        apply out
        apply mem_closedBall_zero_iff.mpr
        apply T.norm_near small (mem_closedBall_zero_iff.mp (region inside))
        rw [dist_comm]
        exact T.upper_corner c here
      · simp [f, image_eq_zero_of_notMem_tsupport inside]
    · rw [T.stair_off c z (fun k hk => occupied ⟨k,hk⟩)]
      exact ⟨by simpa using bpos,fun _ => rfl⟩
  let s := T.spacing^(4*n) * ∑ x : T.Tuple (n:=n), ‖φ (T.rel (T.back x) c)‖
  have pos : 0 ≤ s := mul_nonneg (pow_nonneg T.positive.le _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have represented : (s:ℂ) = ∫ z, T.levels c f z := by
    rw [T.stair_exact]
    simp only [s,f,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sum]
  calc
    _ = s := by simp only [weight,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos T.positive,
      ← Finset.mul_sum,s]
    _ = ‖(s:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos]
    _ = ‖∫ z in U, T.levels c f z‖ := by
      rw [represented,setIntegral_eq_integral_of_forall_compl_eq_zero (s:=U) (fun z => (control z).2)]
    _ ≤ b * volume.real U := norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..).measure_lt_top
      (fun z _ => (control z).1)

/-- The full actual signed test and all angular words have a subpower fee on the original regulator.
All future ultraviolet dates, periods, and common lattice origins may vary. -/
theorem original (simple : G.Simple) {ι : Type} {l : Filter ι} {m : ι → ℕ} (hm : Tendsto m l atTop)
    (N p : ι → ℕ) (hN : ∀ᶠ i in l, m i ≤ N i) (r : ι → ℝ) (rp : ∀ i, 0 < r i)
    (saved : ∀ᶠ i in l, R.family.S.a (m i) ≤ r i) (d : Fin n → ℕ)
    (v : ∀ j, ι → R.family.label (d j)) (hv : ∀ j, RateLE l (ruler R.family m) (v j) 0)
    (φ : Test n) (c : ι → Four ℝ) :
    let T := fun i => mesh R (m i) (p i) (r i) (rp i)
    RateLE l (ruler R.family m) (fun i => ∑ x : (T i).Tuple (n:=n),
      ∑ a : ∀ j, (R.family.labels.level (d j)).Index,
        ‖weight (T i) φ (c i) x * ∏ j, entry R (d j) (m i) (N i) (p i) (r i) (v j i) (a j)‖) 0 := by
  intro T
  obtain ⟨B,nb,invoice⟩ := mass φ
  let s := ruler R.family m
  let test i := ∑ x : (T i).Tuple (n:=n), ‖weight (T i) φ (c i) x‖
  have cash : RateLE l s test 0 := by
    apply (RateLE.const B (large_s R.family hm)).transfer
    filter_upwards [saved] with i hi
    have positive : 0 ≤ test i := Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_eq_abs,abs_of_nonneg positive,Real.norm_eq_abs,abs_of_nonneg nb]
    exact invoice (T i) ((div_le_one (rp i)).2 hi) (c i)
  let e (i : ι) (a : ∀ j, (R.family.labels.level (d j)).Index) : ℂ := ∏ j, entry R (d j) (m i) (N i) (p i) (r i) (v j i) (a j)
  have angular : RateLE l s (fun i => ∑ a, ‖e i a‖) 0 := by
    have trivial : RateLE l s (fun _ : ι => ∑ _k ∈ ({()} : Finset Unit), ‖(1:ℂ)‖) 0 := by
      simpa using RateLE.const (1:ℝ) (large_s R.family hm)
    apply (stencil R simple hm N p hN r saved d v hv (fun _ => ({()} : Finset Unit))
      (fun _ _ => (1:ℂ)) trivial).congr
    apply Eventually.of_forall
    intro i
    simp only [Finset.sum_singleton,one_mul,e]
    apply Finset.sum_congr
    · ext a
      simp only [Finset.mem_univ]
    · intro a _
      rfl
  apply ((cash.mul angular).mono (by norm_num)).congr
  exact Eventually.of_forall fun i => by
    simp only [test, e, Finset.sum_mul, Finset.mul_sum, norm_mul]
    exact Finset.sum_comm

end YM.Integration.WilsonMatrixTicketLanesReportedQuadrature
