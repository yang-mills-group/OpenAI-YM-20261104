import YM.Integration.WilsonMeasuredPublicEntranceFittedSlots
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicGuardFare
open Function Filter Lattice Wilson RG Source Labels
open Extraction Table Spec Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open Next.Foundations OPE.Therm Push.AbsoluteSums.Animals
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonAddressedRestartedColumn WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramBlockedPublicExperiment WilsonAddressedPublicPool
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {ord : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family ord S) (l : Ultrafilter (ℕ×ℕ))


/-- The actually submitted upper column in the fixed physical units of the
    chosen origin and the real scalar wallet of its own marked field. -/
def word (d K:ℕ)(χ:ℝ)(w:R.family.label d):R.family.label d :=
  ((χ:ℂ)⁻¹*((R.family.S.a K:ℂ)^d)⁻¹) • w

theorem cost {d K j:ℕ}{η M χ:ℝ}(positive:0<χ){w:R.family.label d}
    (earned:(R.family.labels.level d).coeffSize w ≤
      stretch R η j K*(2*(R.family.S.a j^d*M))):
    (R.family.labels.level d).coeffSize (word R d K χ w) ≤
        4*(M/χ)*(R.family.S.a j/R.family.S.a K)^((d:ℝ)+η):=by
  let C:=R.family
  have aj:=C.S.a_pos j
  have ak:=C.S.a_pos K
  have pos:=div_pos aj ak
  have time:C.S.scale K-C.S.scale j=Real.log (C.S.a j/C.S.a K):=by
    rw [Schedule.scale,Schedule.scale,Real.log_inv,Real.log_inv,Real.log_div aj.ne' ak.ne']
    ring
  have phase:stretch R η j K=2*(C.S.a j/C.S.a K)^η:=by
    unfold WilsonOriginalMicroscopicGuardedReporters.stretch
    rw [Real.rpow_def_of_pos pos,←time,mul_comm η]
  have normed:(C.labels.level d).coeffSize (word R d K χ w)=
      χ⁻¹*(C.S.a K^d)⁻¹*(C.labels.level d).coeffSize w:=by
    simp only [word,Frame.coeffSize,Pi.smul_apply,norm_smul,norm_mul,norm_inv,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg positive.le,Real.norm_of_nonneg ak.le,Finset.mul_sum,C]
  rw [normed]
  calc
    _ ≤ (χ⁻¹*(C.S.a K^d)⁻¹)*(stretch R η j K*(2*(C.S.a j^d*M))):=
      mul_le_mul_of_nonneg_left earned (mul_nonneg (inv_nonneg.mpr positive.le)
        (inv_nonneg.mpr (pow_nonneg ak.le d)))
    _ = _ := by
      change _=4*(M/χ)*(C.S.a j/C.S.a K)^((d:ℝ)+η)
      rw [phase,Real.rpow_add pos,Real.rpow_natCast,div_pow]
      ring_nf

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (wide : ∀j, 1 ≤ (R.family.path.levels.budget j).supportExponent)
    (quote : Poetry R.family.path.levels) (D target : ℕ) {η : ℝ} (pos : 0<η) :
    ∃ gate : ℕ, ∀ (I : Type) (d : I → Fin (D+1)) (v : (i : I) → S.Field (d i).val)
      (s M : I → ℝ) (L : (i : I) → WilsonMeasuredPublicSlots.Slot F l (d i).val (v i) (s i) (M i))
      (f n N p : ℕ) (_ : ∀i, gate ≤ (L i).j) (before : ∀i, (L i).j ≤ f)
      (live : f+n ≤ N) (_ : ∀i, (L i).j<N),
      ∃ A : (i : I) → R.family.label (d i).val ≃ₗ[ℂ] R.family.label (d i).val,
        (∀i x, Arrived R (d i).val (L i).j (f+n) N p target (by grind) live η (A i) x) ∧
        ∀i, let Y := (L i).arm.source (N,p)
            let w := (A i).symm (fitted R (d i).val (L i).j N p Y)
            (∀χ:ℝ,0<χ → (R.family.labels.level (d i).val).coeffSize (word R (d i).val (f+n) χ w) ≤
              4*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i)/χ)*
                (R.family.S.a (L i).j/R.family.S.a (f+n))^(((d i).val:ℝ)+η)) ∧
              ∀ o, settled R (d i).val (L i).j f n N p live (A i) Y o:=by
  obtain ⟨gate,sales⟩:=WilsonMeasuredPublicEntranceFittedSlots.original R F l simple shop wide quote D target pos
  refine ⟨gate,?_⟩
  intro I d v s M L f n N p late before live deep
  obtain ⟨A,inverse,paid⟩:=sales I d v s M L f n N p late before live deep
  refine ⟨A,inverse,fun i=>?_⟩
  exact ⟨fun χ hp=>cost R hp (paid i).1,(paid i).2⟩

end YM.Integration.WilsonAddressedPublicGuardFare
end
