import YM.Integration.WilsonMatrixTicketLanesChargeSource
import YM.Integration.WilsonMatrixTicketLanesQuota
import YM.OPE.Columns.Reannounce

/-! The physical coefficient price at the reference level and the dual cost of a
moving label at any fixed later level on the given original extraction. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketPhysicalMeshRows

open Filter Next.Rank
open scoped Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {T : Table C.book}

/-- At its own reference level the full engineering charge is the original
coefficient size, uniformly over all later cutoffs and every period. -/
theorem reference (physical : Spec.Final C f T) {d N : ℕ} (per : ℕ)
    (x : C.label d) (hN : C.ref d ≤ N) :
    Spindle.paid C d (C.ref d) N per x * C.S.a (C.ref d) ^ d =
      (C.labels.level d).coeffSize x := by
  rw [WilsonMatrixTicketLanesQuota.quota, Next.UVStress.quota]
  rw [C.normalized physical.room.cutoff hN x]

private theorem norm_le_coeffSize {d : ℕ} (x : C.label d) :
    ‖x‖ ≤ (C.labels.level d).coeffSize x := by
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ _ from Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
  intro i
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- The explicit product of the original column and block charges at this
level controls every physical linear row.  Its value is independent of the
regulating cutoff, period, observing filter, moving label and quota cap. -/
theorem moving (physical : Spec.Final C f T) {d k m : ℕ} (hm : C.ref d ≤ m)
    (u : T.Field d →ₗ[ℂ] ℂ) {l : Filter (ℕ × ℕ)} [l.NeBot] (hl : l ≤ f.fuse)
    (w : ℕ × ℕ → C.label d) (z : C.label d) (q : ℝ) (hw : Tendsto w l (𝓝 z))
    (hq : ∀ᶠ i in l, Next.UVStress.quota C d m i.1 i.2 (w i) ≤ q) :
    ‖u (T.project d z)‖ * C.S.a m ^ (d-k) ≤
      (‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (T.project d))‖ *
        Price.outward C d m * C.S.a m ^ (d-k)) * q := by
  let row := LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (T.project d))
  have hz : ‖z‖ ≤ Price.outward C d m * q := by
    apply le_of_tendsto hw.norm
    filter_upwards [(Next.UVStress.large_mesh f m).filter_mono hl, hq] with i hi hiq
    exact (norm_le_coeffSize (w i)).trans <|
      (Price.at_current C physical.room.cutoff hm hi i.2 (w i)).trans <|
        mul_le_mul_of_nonneg_left hiq (zero_le_one.trans (Price.outward_nn C d m))
  have hr : ‖u (T.project d z)‖ ≤ ‖row‖ * (Price.outward C d m * q) :=
    (row.le_opNorm z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg row))
  calc
    _ ≤ (‖row‖ * (Price.outward C d m * q)) * C.S.a m ^ (d-k) :=
      mul_le_mul_of_nonneg_right hr (pow_nonneg (C.S.a_pos m).le _)
    _ = _ := by dsimp [row]; ring

/-- The physical mesh cancels each block factor at zero tier.  The remaining
column product is common to all horizons and is measured on the original clock. -/
theorem cancelBlocks (C : Family G) (d m : ℕ) :
    Price.outward C d m * C.S.a m ^ d = OPE.Columns.juice C.path.levels m := by
  unfold Price.outward OPE.Columns.juice
  induction m with
  | zero => simp
  | succ m ih =>
    have hb : ((C.S.block m).val : ℝ) ≠ 0 := by
      exact_mod_cast (C.S.block m).property.ne'
    simp only [Finset.prod_range_succ, C.S.a_step, div_pow]
    rw [← ih]
    field_simp [hb]

/-- At zero tier the same subpower column product controls all grades, all
linear rows and all moving labels of this supplied physical final. -/
theorem tierZero (physical : Spec.Final C f T) :
    MergeProof.Ribbons.Note C.S (OPE.Columns.juice C.path.levels) 0 ∧
    ∀ (d m : ℕ), C.ref d ≤ m → ∀ (u : T.Field d →ₗ[ℂ] ℂ)
      (l : Filter (ℕ × ℕ)), l.NeBot → l ≤ f.fuse →
      ∀ (w : ℕ × ℕ → C.label d) (z : C.label d) (q : ℝ), Tendsto w l (𝓝 z) →
      (∀ᶠ i in l, Next.UVStress.quota C d m i.1 i.2 (w i) ≤ q) →
      ‖u (T.project d z)‖ * C.S.a m ^ d ≤
        (‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (T.project d))‖ *
          OPE.Columns.juice C.path.levels m) * q := by
  refine ⟨MergeProof.Ribbons.futon C, ?_⟩
  intro d m hm u l hne hl w z q hw hq
  letI := hne
  have h := moving physical (k := 0) hm u hl w z q hw hq
  rw [Nat.sub_zero, mul_assoc _ (Price.outward C d m) _, cancelBlocks] at h
  exact h

end YM.Integration.WilsonMatrixTicketPhysicalMeshRows
end

