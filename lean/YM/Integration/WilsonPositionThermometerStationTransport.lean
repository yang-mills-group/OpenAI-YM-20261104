import YM.Integration.WilsonPositionThermometerOrientedStation
import YM.Next.RANK.Matrices

/-! Move the literal original cutoff vector between the extraction station
and the reporting date. The engineering factor is canceled on the same
reference column at each step of the actual factory. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationTransport
open Function Set Filter Source RG Lattice Wilson Cells MeasureTheory Next.Rank
open MergeProof.East Next.UVStress Climb
open scoped Classical BigOperators
variable {G : Gauge} (C : Family G) {d N p m k : ℕ}

private theorem size_awake (j d N p : ℕ) (v : C.book.Ref d) :
    (C.labels.level d).coeffSize (Price.awake C d j N p v) =
    ((C.S.a j)^d)⁻¹ * (C.labels.level d).coeffSize (Price.columns C d j N p v) := by
  simp only [Price.awake, Labels.Frame.coeffSize, Pi.smul_apply, norm_smul, ← Finset.mul_sum,
    norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos j).le]

theorem adjacent (hC : C.Makes) (hm : C.ref d ≤ m) (hn : m < N) (v : C.book.Ref d) :
    (C.labels.level d).coeffSize (Price.awake C d m N p v) ≤
      (C.path.levels.params (m+1)).columns * (C.labels.level d).coeffSize (Price.awake C d (m+1) N p v) := by
  let T := C.factory d N p
  have paid : T.Based _ _ _ := hC.calibrated d N p (hm.trans hn.le)
  have step := paid.front m hm hn (T.terminal.symm v)
  have scale : C.S.a m = ((C.S.block m).val : ℝ) * C.S.a (m+1) := by
    rw [C.S.a_step, mul_div_cancel₀ _ (by exact_mod_cast (C.S.block m).property.ne')]
  rw [size_awake, size_awake]
  apply (mul_le_mul_of_nonneg_left step (inv_nonneg.mpr (pow_nonneg (C.S.a_pos m).le d))).trans_eq
  change ((C.S.a m)^d)⁻¹ * (_ * ((C.S.block m).val : ℝ)^d * _) =
    (C.path.levels.params (m+1)).columns * (((C.S.a (m+1))^d)⁻¹ * _)
  rw [scale, mul_pow, mul_inv_rev]
  have positive : ((C.S.block m).val : ℝ) ≠ 0 := by exact_mod_cast (C.S.block m).property.ne'
  field_simp [positive,(C.S.a_pos (m+1)).ne']
  rfl

theorem interval (hC : C.Makes) (hm : C.ref d ≤ m) (hmk : m ≤ k) (hn : k ≤ N)
    (v : C.book.Ref d) (ε : ℝ)
    (admitted : ∀ i, m ≤ i → i < k → (C.path.levels.params (i+1)).columns ≤ ((C.S.block i).val : ℝ)^ε) :
    (C.labels.level d).coeffSize (Price.awake C d m N p v) ≤
      (C.S.a m / C.S.a k)^ε * (C.labels.level d).coeffSize (Price.awake C d k N p v) := by
  induction k,hmk using Nat.le_induction with
  | base => rw [div_self (C.S.a_pos m).ne',Real.one_rpow,one_mul]
  | succ i hmi rec =>
    have pre := rec (Nat.le_trans (Nat.le_succ i) hn) (fun j hj hi => admitted j hj (hi.trans (Nat.lt_succ_self i)))
    have line := adjacent (p:=p) C hC (hm.trans hmi) (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hn) v
    have next := line.trans (mul_le_mul_of_nonneg_right (admitted i hmi (Nat.lt_succ_self i))
      (by unfold Labels.Frame.coeffSize; positivity))
    apply pre.trans ((mul_le_mul_of_nonneg_left next (Real.rpow_nonneg (div_nonneg
      (C.S.a_pos m).le (C.S.a_pos i).le) ε)).trans_eq ?_)
    rw [← mul_assoc, ← Real.mul_rpow (div_nonneg (C.S.a_pos m).le (C.S.a_pos i).le) (Nat.cast_nonneg _)]
    have changeScale : C.S.a m / C.S.a i * ((C.S.block i).val : ℝ) = C.S.a m / C.S.a (i+1) := by
      rw [C.S.a_step,div_div_eq_mul_div]
      ring
    rw [changeScale]

/-- The source at both dates is the same actual station lift for each field
slot, including its sign. Period and upper cutoff are fixed throughout. -/
theorem filed {D : ℕ} (V : Vane C D) (j : Fin (D+1)) (w : (Bel C.book).Field j)
    (hC : C.Makes) (hm : C.ref j ≤ m) (live : m ≤ V.k) (upper : V.k ≤ N) (ε : ℝ)
    (admitted : ∀ i, m ≤ i → i < V.k → (C.path.levels.params (i+1)).columns ≤ ((C.S.block i).val : ℝ)^ε) :
    let v := V.wheel.atCut (N,p) j w
    (C.labels.level j).coeffSize (Price.awake C j m N p v) ≤
      (C.S.a m / C.S.a V.k)^ε * (C.labels.level j).coeffSize (Price.awake C j V.k N p v) :=
  interval C hC hm live upper _ ε admitted

end YM.Integration.WilsonPositionThermometerStationTransport
end
