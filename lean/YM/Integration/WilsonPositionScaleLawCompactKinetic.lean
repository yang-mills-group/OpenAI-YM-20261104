import YM.Integration.WilsonPositionScaleLawKinetic
import YM.Integration.WilsonPositionScaleLawCompactIndependent
import YM.Integration.WilsonPositionScaleLawCompactJacobian

/-! Local inverse estimate for the real physical measured fields and predeclared scale matrix on an arbitrary positive compact window. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactKinetic
open Function Filter Set Finset PowerSeries Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (exactOp)
open WilsonPositionScaleLawCompactJacobian (fieldsAt)
open WilsonPositionScaleLawIndependent (B trial)
open WilsonPhysicalPositionBornCandidates (operator record expansion)
open scoped Topology BigOperators Classical
variable [Win:RangeSpec] {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

abbrev kinetic:=WilsonPositionHomogeneousFrame.reading F J Z

def residual (d q:ℕ)(z:ℝ×Ratio):MoveSpace G d:=
  let D:=Z.store.survey d
  D.itinerary (D.purse (fieldsAt F J Z.store d z),trial Z M ν d q (WilsonPositionScaleLawCompactIndependent.time z.2) (kinetic Z F J z.1))-D.itinerary D.opening

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include H paid lead in
theorem quantitative (d q:ℕ)(raw:WilsonPositionScaleLawCompactBranch.Raw J d):∃L:ℝ,0≤L ∧ ∀ᶠz in sweep,
    ‖exactOp F J Z.store d z-WilsonPhysicalPositionBornCandidates.operator R.family (trial Z M ν d q (WilsonPositionScaleLawCompactIndependent.time z.2) (kinetic Z F J z.1))‖≤
      L*‖residual Z M ν F J d q z‖:=by
  let D:=Z.store.survey d
  let T:=kinetic Z F J
  let a(z:ℝ×Ratio):=trial Z M ν d q (WilsonPositionScaleLawCompactIndependent.time z.2) (T z.1)
  let X:=(Bel R.family.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  let A:MoveSpace G d→L[ℝ](X→L[ℂ]X):=(record G R.family d).toContinuousLinearMap
  have ht:Tendsto T trail (𝓝 0):=WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion
  have ha:Tendsto a sweep (𝓝 0):=WilsonPositionScaleLawCompactIndependent.small Z M H ν d q ht
  obtain ⟨L,hL,fee⟩:=WilsonPositionPrescribedStability.residual D (Z.store.prepared d)
    (WilsonPositionScaleLawWindow.original F J Z.store lead d) ha
  refine ⟨‖A‖*L,mul_nonneg (norm_nonneg _) hL,?_⟩
  filter_upwards [WilsonPositionScaleLawCompactNative.realizes F J Z.store lead d,
    WilsonPositionScaleLawCompactJacobian.recovered F J Z.store lead d raw,fee] with z exactField fit loan
  have diff(u v:MoveSpace G d):WilsonPhysicalPositionBornCandidates.operator R.family u-WilsonPhysicalPositionBornCandidates.operator R.family v=A (u-v):=by
    rw [expansion,expansion,A.map_sub];change _=record G R.family d u-record G R.family d v;abel
  rw [←exactField,diff,show WilsonPositionScaleLawCompactNative.coordinates F J Z.store d z=_ from fit,mul_assoc]
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left loan (norm_nonneg _))

end YM.Integration.WilsonPositionScaleLawCompactKinetic
end
