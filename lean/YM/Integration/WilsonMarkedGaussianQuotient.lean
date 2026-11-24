import YM.Integration.WilsonMarkedFiniteWickDefect

/-! A single original external mark, with every coupling coefficient retained.
The two separately normalized Gaussian conditionals can be compared by their
unnormalized vacuum and marked moments, taken before any division. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedGaussianQuotient

open Marker Multi Comparison.RG02 Order Extra.Trajectories Primitives.GCC.Anchor
open Lattice RG Tree Wilson Exterior Precision Stationary MeasureTheory Next.SectorChange Finset
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {I : Census V} {p : ℕ}

omit [Fintype V] in
private theorem outside (s u : I.Mode) {v : V} (h : Poly.merges s u (I.fire v))
    (hv : v ∈ u.val) : s = I.quiet := by
  apply Subtype.ext
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have mem : z ∈ (I.fire v).val := h.2 ▸ Finset.mem_union.mpr (Or.inl hz)
  have eq : z=v := Finset.mem_singleton.mp mem
  exact Finset.disjoint_left.mp h.1 hz (eq.symm ▸ hv)

private theorem marked_product (v : V) (u : Index p) (x y : Grade I p) :
    (x * Cumulants.highlight (Sum.inl v) y).part (Join.pair (I.fire v) u) =
      (denominator x * Cumulants.highlight (Sum.inl v) y).part (Join.pair (I.fire v) u) := by
  rw [Join.pair_product,Join.pair_product]
  apply sum_congr rfl;intro s _
  apply sum_congr rfl;intro t _
  apply sum_congr rfl;intro w _
  apply sum_congr rfl;intro z _
  by_cases both : Poly.merges s w (I.fire v) ∧ Poly.merges t z u
  · simp only [if_pos both]
    by_cases how : v∈w.val
    · have vacant := outside s w both.1 how
      subst s
      rw [denominator,bottom_value,if_pos rfl]
    · have empty : Sum.inl v ∉ (Join.pair w z).val := by simpa [Join.pair] using how
      rw [Cumulants.highlight_part,if_neg empty,mul_zero,mul_zero]
  · simp [both]

/-- The physical connected and normalized moment coefficients at one true
external label agree even in the presence of arbitrarily many coupling slots. -/
theorem connected (x : Grade I p) (h : UnitLeading x) (v : V) (u : Index p) :
    (Order.logMarked x).part (Join.pair (I.fire v) u) =
      (Order.ratio x).part (Join.pair (I.fire v) u) := by
  have on : Sum.inl v ∈ (Join.pair (I.fire v) u).val := by simp [Join.pair,Census.fire]
  have root := congrArg (fun y : Grade I p => y.part (Join.pair (I.fire v) u))
    (Cumulants.moment_root (Sum.inl v) (Order.ratio x) (Order.ratio_quiet h))
  rw [marked_product,Order.denominator,Order.ratio_pure h,one_mul] at root
  simpa only [Order.logMarked,Cumulants.highlight_part,if_pos on] using root.symm

theorem coefficient (x : Grade I p) (h : UnitLeading x) (v : V) (e : ℕ) :
    (Order.observe I p (Order.logMarked x) e).part (I.fire v) =
      (Order.observe I p (Order.ratio x) e).part (I.fire v) := by
  by_cases he : e ≤ p
  · unfold Order.observe
    simp only [if_pos he,Poly.part_smul]
    exact congrArg _ (connected x h v _)
  · simp [Order.observe,he]

omit [Fintype V] in
private theorem vacuum_factor (a b : Poly I) (s : I.Mode) :
    (Order.blanked I a * b).part s = a.part I.quiet * b.part s := by
  change ((algebraMap ℂ (Poly I)) (a.part I.quiet) * b).part s = _
  rw [←Algebra.smul_def,Poly.part_smul]

/-- The complete triangular recurrence at every ordinary coupling order. The
coefficient at the original single external coordinate is determined uniquely
by its marked raw numerator and the unmarked raw numerator. -/
theorem division (x : Grade I p) (hx : UnitLeading x) (sx : Order.Symmetric x)
    (v : V) {e : ℕ} (he : e ≤ p) :
    (Order.observe I p x e).part (I.fire v) =
      ∑ j ∈ range (e+1), (Order.observe I p x j).part I.quiet *
        (Order.observe I p (Order.logMarked x) (e-j)).part (I.fire v) := by
  obtain ⟨L,logs⟩ := Order.sym_ratio hx sx
  obtain ⟨P,arr⟩ := sx
  have mixed : Order.series I p ((PowerSeries.map (Order.blanked I) P)*L) = x := by
    rw [map_mul,←Order.bottom_map,arr,logs]
    exact Order.recovers hx
  conv_lhs => rw [←mixed,Order.observation _ _ _ he,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Poly.part_sum]
  apply sum_congr rfl
  intro j hj
  have je : j ≤ e := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [PowerSeries.coeff_map,vacuum_factor,coefficient x hx v,←logs,Order.observation _ _ _ (le_trans (Nat.sub_le ..) he)]
  rw [←arr,Order.observation _ _ _ (le_trans je he)]

section
variable {G : Gauge} {c s : Side} {S : StepData c s} {cut : Clip} {A : PathData G} {o : ChartRatio G}
    (K : Bulk.Kernel S cut A o) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors I G s) (b : Bid.Dir G c)

/-- The actual finite stationary Wilson Gaussian integral (prior to taking a
vacuum or marked logarithm), including the unmarked action and all its jets. -/
def moment (s₀ : I.Mode) (e : ℕ) : ℂ :=
  ∫ z, Assembly.rows (Assembly.expansions W.power (Bulk.markFn S F W) (Bulk.geometric K F t W))
    s₀ e (Bulk.translated K F b z) ∂Gaussian.cloud (K.covariance F t)

private theorem integral (s₀ : I.Mode) {e : ℕ} (he : e ≤ p) :
    (Order.observe I p (Bulk.Fk K F t W b p) e).part s₀ = moment K F t W b s₀ e :=
  Assembly.order_read _ _ _ _ _ _ _ (K.positive F t) s₀ he

/-- Cross multiplication before vacuum division. For an independently
computed formal vacuum Q and marked conditional T, the remaining input is
exactly the difference of the two unnormalized Wick products displayed on
the left. The other marked coordinates of the submitted finite menu do not
occur in the vacuum factors. -/
theorem crossed (v : V) {e : ℕ} (he : e ≤ p) (Q T : PowerSeries ℂ) :
    let N := PowerSeries.mk (moment K F t W b (I.fire v))
    let Z := PowerSeries.mk (moment K F t W b I.quiet)
    let X := Bulk.Fk K F t W b p
    let M := PowerSeries.mk (fun j => (Order.observe I p (Order.logMarked X) j).part (I.fire v))
    PowerSeries.coeff e (Q*N-Z*(Q*T)) = PowerSeries.coeff e ((Q*Z)*(M-T)) := by
  intro N Z X M
  have agree (j : ℕ) (hj : j ≤ p) : PowerSeries.coeff j N = PowerSeries.coeff j (Z*M) := by
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [show PowerSeries.coeff j N = moment K F t W b (I.fire v) j from PowerSeries.coeff_mk _ _]
    rw [←integral K F t W b _ hj,division X (Bulk.fk_unit ..) (Bulk.fk_sym ..) v hj]
    apply sum_congr rfl
    intro k hk
    have kh : k ≤ j := Nat.le_of_lt_succ (mem_range.mp hk)
    simp only [Z,M,PowerSeries.coeff_mk]
    rw [integral K F t W b _ (kh.trans hj)]
  have zero : PowerSeries.coeff e (Q*(N-Z*M))=0 := by
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply sum_eq_zero
    intro k _
    rw [map_sub,agree _ ((Nat.sub_le ..).trans he),sub_self,mul_zero]
  have subtract : Q*N-Z*(Q*T) - (Q*Z)*(M-T) = Q*(N-Z*M) := by ring
  exact sub_eq_zero.mp (show _ - _ = 0 by rw [←map_sub,subtract,zero])

end
end YM.Integration.WilsonMarkedGaussianQuotient

