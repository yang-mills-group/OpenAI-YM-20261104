import YM.Integration.ActualCanonicalScheduledPayloadPrice

/-! Exact extraction of the inherited coefficient from the same canonical
regular invoice. These identities and the existing scheduled upper bound
supply no contraction estimate for that coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualNextInheritedPrice
open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open IterationFour
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric

variable {G : Gauge}

/-- At zero reset parameter the complete regular invoice is linear in its
original source price. Both the low and high correction rows remain. -/
theorem regularNeed_linear (p : BudgetPoint) (c : Clip) (sigma C H : Real) :
    CappedRegularReset.regularNeed G p c sigma C 0 H =
      CappedRegularReset.regularNeed G p c sigma C 0 1 * H := by
  simp only [CappedRegularReset.regularNeed, abs_zero, zero_mul, zero_add,
    mul_one, one_mul]
  ring

/-- The actual requested-norm extraction factor, before any polynomial
majorant or payment is applied. -/
def extractionFactor {V : Type} {J : Request V} (run : Run G)
    (A : NumericSchedule run.family J) (m : Nat) : Real :=
  CappedRegularReset.regularNeed G (A.outputNorm m)
    (run.family.path.levels.params m).clip
    (run.family.path.levels.params m).width
    (run.family.path.levels.params m).paths 0 1

section Actual
variable (run : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities}
    {Y : YM.Comparison.RG02.Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : Real}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

/-- The same error price, with no regular row or source term removed. -/
theorem errorPrice_eq :
    ActualCanonicalInputPayload.errorPrice run I K =
      extractionFactor run A datum.level *
        ActualSelectedVacuumGerm.sourcePrice run I K := by
  exact regularNeed_linear (A.outputNorm datum.level)
    (run.family.path.levels.params datum.level).clip
    (run.family.path.levels.params datum.level).width
    (run.family.path.levels.params datum.level).paths
    (ActualSelectedVacuumGerm.sourcePrice run I K)

/-- Inherited error, Taylor error and calibration retain their separate
literal coefficients on the original family and selected input. -/
theorem errorPrice_terms :
    ActualCanonicalInputPayload.errorPrice run I K =
      extractionFactor run A datum.level *
        (K.vacuumConstant / ((run.family.S.block datum.level).val : Real) +
          K.vanishing datum.level) * I.inherited +
      extractionFactor run A datum.level *
        Currency.g run.family datum.cutoff datum.period (datum.level + 1) ^
          (J.order + 1) * K.geometry datum.level +
      extractionFactor run A datum.level * K.geometry datum.level * eta_w := by
  rw [errorPrice_eq]
  dsimp only [ActualSelectedVacuumGerm.sourcePrice, LocalComparison.vacuumRate]
  ring

/-- The already-paid polynomial majorant separates the inherited term from
both fresh terms. The inherited coefficient is not asserted to be small. -/
theorem scheduled_split (S : Retained.Chosen K I M) :
    let P := ActualCanonicalPayloadPrice.coefficient G (A.outputNorm 0) *
      A.admittedCost datum.level ^
        ActualCanonicalPayloadPrice.degree (A.outputNorm 0)
    ActualCanonicalInputPayload.errorPrice run I K <=
      P * ((K.vacuumConstant / ((run.family.S.block datum.level).val : Real) +
        K.vanishing datum.level) * I.inherited) +
      P * (Currency.g run.family datum.cutoff datum.period (datum.level + 1) ^
        (J.order + 1) * K.geometry datum.level + K.geometry datum.level * eta_w) := by
  dsimp only
  calc
    _ <= ActualCanonicalPayloadPrice.coefficient G (A.outputNorm 0) *
        A.admittedCost datum.level ^
          ActualCanonicalPayloadPrice.degree (A.outputNorm 0) *
        ActualSelectedVacuumGerm.sourcePrice run I K :=
      ActualCanonicalPayloadPrice.scheduled_price run S
    _ = _ := by
      dsimp only [ActualSelectedVacuumGerm.sourcePrice, LocalComparison.vacuumRate]
      ring

end Actual
end YM.Integration.ActualNextInheritedPrice
end
