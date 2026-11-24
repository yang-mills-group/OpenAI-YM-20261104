import YM.Integration.WilsonPositionScaleLawIndependent
import YM.Integration.WilsonPositionHomogeneousLeading

/-! The charge is the actual signed kinetic reading on the position-calibrated
original Wilson tower. A numerical bill for its finite, prescribed equations
controls the full bounded-ratio scale operator in the native MS gaugeB frame. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawKinetic
open Function Filter Set Finset PowerSeries Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawJacobian (fieldsAt)
open WilsonPositionScaleLawIndependent (B trial)
open WilsonPhysicalPositionBornCandidates (operator record expansion)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

private def evalAt {d:ℕ}(v:Sec G d):Change G d→ₗ[ℝ]Sec G d where
  toFun x:=x.val v
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private theorem stages {U:Type*}[AddCommMonoid U](q:ℕ)(u:ℕ→U):
    (∑k:Fin (q+1),u k.val)=u 0+∑j∈range q,u (j+1):=by
  rw [Fin.sum_univ_eq_sum_range,Finset.sum_range_succ',add_comm]

include H in
theorem field (d q:ℕ)(s g:ℝ)(v:Sec G d):
    WilsonPhysicalPositionDiscreteBranches.field (trial Z M ν d q s g) v=
      ∑k:Fin (q+1),(g:ℂ)^k.val • coeff k.val (B Z M ν s d) v:=by
  rw [stages q (fun k=>(g:ℂ)^k • coeff k (B Z M ν s d) v),(H.details.normative ν).first.paid s d |>.zero,
    pow_zero,one_smul,WilsonPhysicalPositionDiscreteBranches.field,stood]
  change v+evalAt v ((guide G d).symm (∑j∈range q,g^(j+1) • guide G d (WilsonPositionScaleLawIndependent.letter Z M ν d j s)))=_
  rw [map_sum,map_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [map_smul,LinearEquiv.symm_apply_apply,map_smul,←Complex.ofReal_pow]
  change _ • (WilsonPositionScaleLawIndependent.letter Z M ν d j s).val v=_
  rw [WilsonPositionScaleLawIndependent.filled Z M H ν]
  rfl

include H in
theorem grades {d e:ℕ}(h:d≤e)(q:ℕ)(s g:ℝ)(v:Sec G d):
    WilsonPhysicalPositionDiscreteBranches.field (trial Z M ν e q s g) (up h v)=
      up h (WilsonPhysicalPositionDiscreteBranches.field (trial Z M ν d q s g) v):=by
  rw [field Z M H ν,field Z M H ν,map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_smul,(H.details.normative ν).first.continues s h]

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

abbrev kinetic:=WilsonPositionHomogeneousFrame.reading F J Z

def residual (d q:ℕ)(z:ℝ×Ratio):MoveSpace G d:=
  let D:=Z.store.survey d
  D.itinerary (D.purse (fieldsAt F J Z.store d z),trial Z M ν d q (WilsonPositionScaleLawIndependent.time z.2) (kinetic Z F J z.1))-D.itinerary D.opening

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include H paid lead in
theorem quantitative (d q:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d):∃L:ℝ,0≤L ∧ ∀ᶠz in sweep,
    ‖exactOp F J Z.store d z-WilsonPhysicalPositionBornCandidates.operator R.family (trial Z M ν d q (WilsonPositionScaleLawIndependent.time z.2) (kinetic Z F J z.1))‖≤
      L*‖residual Z M ν F J d q z‖:=by
  let D:=Z.store.survey d
  let T:=kinetic Z F J
  let a(z:ℝ×Ratio):=trial Z M ν d q (WilsonPositionScaleLawIndependent.time z.2) (T z.1)
  let X:=(Bel R.family.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  let A:MoveSpace G d→L[ℝ](X→L[ℂ]X):=(record G R.family d).toContinuousLinearMap
  have ht:Tendsto T trail (𝓝 0):=WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion
  have ha:Tendsto a sweep (𝓝 0):=WilsonPositionScaleLawIndependent.small Z M H ν d q ht
  obtain ⟨L,hL,fee⟩:=WilsonPositionPrescribedStability.residual D (Z.store.prepared d)
    (WilsonPositionScaleLawHome.original F J Z.store lead d) ha
  refine ⟨‖A‖*L,mul_nonneg (norm_nonneg _) hL,?_⟩
  filter_upwards [WilsonPositionScaleLawNative.realizes F J Z.store lead d,
    WilsonPositionScaleLawJacobian.recovered F J Z.store lead d raw,fee] with z exactField fit loan
  have diff(u v:MoveSpace G d):WilsonPhysicalPositionBornCandidates.operator R.family u-WilsonPhysicalPositionBornCandidates.operator R.family v=A (u-v):=by
    rw [expansion,expansion,A.map_sub];change _=record G R.family d u-record G R.family d v;abel
  rw [←exactField,diff,show WilsonPositionScaleLawNative.coordinates F J Z.store d z=_ from fit,mul_assoc]
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left loan (norm_nonneg _))

end YM.Integration.WilsonPositionScaleLawKinetic
end
