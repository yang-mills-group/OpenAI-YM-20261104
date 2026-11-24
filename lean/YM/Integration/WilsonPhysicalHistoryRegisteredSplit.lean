import YM.Integration.WilsonInheritedRegisteredField
import YM.Integration.ActualWilsonAbsoluteTransport

/-! The separately normalized regular and forced portions of the actual translated factory
insertion, with the engineering factor at its own physical date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonInheritedRegisteredField
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Push.Local MergeProof
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} (h : C.Makes) {N per k d : ℕ}

def regular (hk : k ≤ N) (w : C.label d) (o : Site (C.side k per))
    (U : Config G (C.side k per)) : ℂ :=
  alto C.path k d * (packet h hk w o).exponentialEntry o (C.localSection d) (C.path.rep N per k) U

def forced (hk : k ≤ N) (w : C.label d) (o : Site (C.side k per))
    (U : Config G (C.side k per)) : ℂ :=
  let A := C.path.rep N per k
  let Z := packet h hk w o
  alto C.path k d * ((∑' b, Z.marked A b U)/(A.activities.gas A.p U : ℂ))

theorem separated (hk : k ≤ N) (w : C.label d) (o : Site (C.side k per)) (U : Config G (C.side k per)) :
    field h hk w o U=regular h hk w o U+forced h hk w o U := by
  let A := C.path.rep N per k
  let Z := packet h hk w o
  have pos : (A.eval U : ℂ) ≠ 0 := by exact_mod_cast (Multi.AxisShift.chosen_positive h.wilson hk U).ne'
  have value : (A.eval U : ℂ)=(Real.exp (A.exponent U):ℂ)*(A.activities.gas A.p U:ℂ) :=
    Complex.ofReal_mul _ _
  have ee : (Real.exp (A.exponent U):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have gg := (mul_ne_zero_iff.mp (value ▸ pos)).2
  change _*Z.density o (C.localSection d) A U/(A.eval U:ℂ) =
    _*Z.exponentialEntry o (C.localSection d) A U + _*((∑' b,Z.marked A b U)/(A.activities.gas A.p U:ℂ))
  rw [Coefficient.density,value]
  field_simp [ee,gg]

theorem regular_envelope (hk : k ≤ N) (hr : C.ref d ≤ k) (w : C.label d) (o : Site (C.side k per)) :
    Envelope (regular h hk w o) := by
  let A := C.path.rep N per k
  let Z := packet h hk w o
  let S := C.localSection d
  let v := (C.labels.level d).scaled A.p.threshold⁻¹ ((C.labels.level d).core Z.x)
  let primary := masked A.p.threshold (S.footprint o) (S.places v o)
  have billed := WilsonTranslatedFactory.based h hr hk o ((C.factory d N per).terminal.symm w)
  have format : Z.Format o C.params A := billed.1
  have tails := Coefficient.regular_series billed.2
  have smooth := S.continuous_places v o
  have mPrimary : Measurable primary := masked_measurable _ _ _ smooth.measurable
  obtain ⟨M,hM⟩ := (isCompact_range smooth.norm).bddAbove
  have cap (U) : ‖primary U‖ ≤ max M 0 := by
    by_cases clean : Healthy A.p.threshold (S.footprint o) U
    · rw [show primary U=S.places v o U from masked_eq _ _ _ _ clean]
      exact (hM ⟨U,rfl⟩).trans (le_max_left _ _)
    rw [show primary U=0 from masked_ne _ _ _ _ clean,norm_zero]
    exact le_max_right _ _
  have terms : Measurable (fun U=>∑' j,Z.maskedTerm A j U) :=
    Measurable.tsum fun j=>masked_measurable _ _ _ (format.smooth j).borel
  obtain ⟨D,hD⟩:=tails.bound
  have fee (U) : ‖Z.exponentialEntry o S A U‖ ≤ ‖Z.x 0‖+max M 0+D := by
    change ‖Z.x 0+primary U+∑' j,Z.maskedTerm A j U‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (le_refl _) (cap U))) (hD U))
  refine ⟨measurable_const.mul ((measurable_const.add mPrimary).add terms),
    ‖alto C.path k d‖*(‖Z.x 0‖+max M 0+D),?_⟩
  intro U
  change ‖alto C.path k d * Z.exponentialEntry o S A U‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (fee U) (norm_nonneg _)

theorem weighted (hk : k ≤ N) (hr : C.ref d ≤ k) (w : C.label d) (o : Site (C.side k per)) :
    let A := C.path.rep N per k
    Integrable (fun U=>A.eval U • regular h hk w o U) (prior G _) ∧
    Integrable (fun U=>A.eval U • forced h hk w o U) (prior G _) := by
  intro A
  let Z := packet h hk w o
  let S := C.localSection d
  have soft := ActualWilsonAbsoluteTransport.weighted C h hk (regular_envelope h hk hr w o)
  have sale := WilsonTranslatedFactory.based h hr hk o ((C.factory d N per).terminal.symm w)
  have full : Integrable (Z.density o S A) (prior G _) :=
    (Z.envelope S (h.wilson.represents N per k hk).good sale.2 sale.1).integrableC _
  have lifted : Integrable (fun U=>A.eval U • field h hk w o U) (prior G _) := by
    apply (full.smul (alto C.path k d)).congr (ae_of_all _ fun U=>?_)
    have nz : (A.eval U:ℂ)≠0 := by exact_mod_cast (Multi.AxisShift.chosen_positive h.wilson hk U).ne'
    change _*Z.density o S A U=(A.eval U:ℂ)*(_*Z.density o S A U/(A.eval U:ℂ))
    field_simp
  refine ⟨soft,(lifted.sub soft).congr (ae_of_all _ fun U=>?_)⟩
  change A.eval U • field h hk w o U-A.eval U • regular h hk w o U=A.eval U • forced h hk w o U
  rw [separated,smul_add];abel

end YM.Integration.WilsonInheritedRegisteredField
end
