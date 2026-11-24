import YM.RG12.Canonical.Ticket
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size

/-! Actual all-calendar log quota at every degree below four. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Lattice RG Source
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {hC : C.Makes} {φ : Filter UVIndex} [φ.NeBot]
  {M : ∀ d : ℕ, ℕ → RepChart C d}

variable (hG : G.Simple) (h : Observing C hC φ M)

lemma mass_unit (d k : ℕ) (z : ℂ) :
    mass C d (z • unitVec (C.labels.level d) C.path k) = ‖z‖ * C.S.a k ^ d := by
  simp [mass, Labels.Frame.coeffSize,unitVec, Labels.Frame.e0,Pi.single_apply,
    mul_ite, apply_ite (Norm.norm : ℂ → ℝ), Complex.norm_real,
    Real.norm_of_nonneg (C.path.S.a_pos _).le]

omit [φ.NeBot] in
lemma atK_unit (hC : C.Makes) (d k : ℕ) (i : UVIndex) (he : C.ref d ≤ k) (hi : k ≤ i.1) :
    atK C hC d k i (unitVec (C.labels.level d) C.path k) = C.refUnit d := by
  let T := C.factory d i.1 i.2; let F := C.labels.level d
  have ht : T.Based _ _ _ := hC.calibrated d i.1 i.2 (he.trans hi)
  change (charts C hC d k i).symm _ = _
  apply (charts C hC d k i).injective; rw [LinearEquiv.apply_symm_apply,charts,dif_pos ⟨he,hi⟩]
  change _ = (T.entries k (T.terminal.symm (C.refUnit d))).x
  rw [show C.refUnit d = T.terminal (unitVec F C.path i.1) from
    (ht.unit_coord _ le_rfl (he.trans hi)).symm.trans (ht.reads _),
    LinearEquiv.symm_apply_apply]; exact (ht.unit_coord k he hi).symm

include h
theorem Observing.unit (d k : ℕ) (he : C.ref d ≤ k) :
    M d k (unitVec (C.labels.level d) C.path k) = C.refUnit d :=
  tendsto_nhds_unique_of_eventuallyEq (h.columns _ _ he _ le_rfl) tendsto_const_nhds
    ((h.grows.eventually_ge_atTop k).mono fun _ hi => atK_unit _ _ _ _ he hi)

include hG
omit h in
lemma unit_spans (C : Family G) (d k : ℕ) (hd : d < 4) (x : C.label d) :
    ∃ z : ℂ, x = z • unitVec (C.labels.level d) C.path k := by
  let F := C.labels.level d; let a := (C.S.a k : ℂ) ^ d
  have ha : a ≠ 0 := pow_ne_zero _ (by exact_mod_cast (C.S.a_pos k).ne')
  obtain ⟨t,ht⟩ := YM.UVNext.FreeStress.just_one hG hd (F.coords.symm x)
  have he : x = t • F.e0 := by rw [← F.coords.apply_symm_apply x,ht,map_smul,F.coords_unit]
  exact ⟨t/a, he.trans (smul_smul (t/a) a F.e0 |>.trans (congr_arg (· • F.e0) (div_mul_cancel₀ _ ha))).symm⟩

lemma low_right_price (S : Table C.book) (d : ℕ) (hd : d < 4) : RightPrice C S M d := by
  intro x
  obtain ⟨z,hz⟩ := unit_spans hG C d (C.ref d) hd (S.representative d x)
  refine ⟨1,?_⟩
  filter_upwards [eventually_ge_atTop (C.ref d), (hat_grows (C:=C) hG).eventually_ge_atTop ‖z‖] with k hk ht
  refine ⟨z • unitVec (C.labels.level d) C.path k, ?_, ?_⟩
  · rw [map_smul,h.unit d k hk, ← hz]; exact S.rep ..
  rw [mass_unit,pow_one]; exact (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (C.S.a_pos _).le ((C.S.strictAnti.antitone (Nat.zero_le k)).trans_eq C.S.a_zero))).trans ht

lemma low_row_price (S : Table C.book) (B : DiffPlan S) (hS : S.Basic) (hB : B.Inclusions S)
    (d w : ℕ) (hd : d < 4) : RowPrice C S B M d w := by
  intro L hw hl
  rcases Nat.eq_zero_or_pos w with rfl|he
  · refine ⟨1,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d),
      (hat_grows (C:=C) hG).eventually_ge_atTop ‖L (S.unit d)‖] with k hk ht v
    obtain ⟨z,rfl⟩ := unit_spans hG C d k hd v
    rw [map_smul, h.unit d k hk, map_smul,map_smul, norm_smul, mass_unit, Nat.sub_zero,pow_one]
    change ‖z‖ * ‖L (S.unit d)‖ ≤ _
    apply le_trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
    refine le_of_eq ?_; have ha := pow_ne_zero d (C.S.a_pos k).ne'; field_simp
  refine ⟨0,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d)] with k hk v
  obtain ⟨z,rfl⟩ := unit_spans hG C d k hd v
  have hz := hl 0 he (S.unit 0)
  rw [B.fixs hB hS] at hz
  rw [map_smul,h.unit d k hk,map_smul,map_smul, show S.project d (C.refUnit d)=S.unit d from rfl,
    hz, smul_zero,norm_zero,pow_zero]
  exact mul_nonneg (div_nonneg zero_le_one (pow_nonneg (C.S.a_pos _).le _)) (mass_nonneg ..)
end YM.RG12
