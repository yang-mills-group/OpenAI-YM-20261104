import YM.Integration.WilsonPositionScaleLawQinter
import YM.Integration.WilsonPositionScaleLawCompactPolynomial
import YM.Integration.WilsonPositionScaleLawCompactKinetic

/-! Original positive-order operator estimate on every compact interval of positive length ratios. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactQinter
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (exactOp)
open WilsonPositionScaleLawCompactJacobian (fieldsAt)
open WilsonPositionScaleLawIndependent (trial)
open WilsonPositionScaleLawCompactPolynomial (pre logRatio)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics
variable [Win:RangeSpec] {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)


open private combine from YM.Integration.WilsonPositionScaleLawQinter

abbrev digits (d q:ℕ)(z:ℝ×Ratio):=trial Z M ν d q (logRatio z.2) (kinetic Z F J z.1)

def prediction (d q:ℕ)(z:ℝ×Ratio):=WilsonPhysicalPositionBornCandidates.operator R.family (digits Z M ν F J d q z)

def measured (d q:ℕ)(z:ℝ×Ratio): (Z.store.survey d).Bag:=
  let D:=Z.store.survey d
  D.purse (fieldsAt F J Z.store d z)-D.purse (pre Z M ν d q z.2 (kinetic Z F J z.1))

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include H lead paid in
theorem original (d q:ℕ)(raw:WilsonPositionScaleLawCompactBranch.Raw J d):∃L A:ℝ,0≤L ∧ 0≤A ∧ ∀ᶠz in sweep,
    ‖exactOp F J Z.store d z-prediction Z M ν F J d q z‖≤
      L*‖measured Z M ν F J d q z‖+A*|kinetic Z F J z.1|^(q+1):=by
  let D:=Z.store.survey d
  let T:=kinetic Z F J
  let a:=digits Z M ν F J d q
  have ht:Tendsto T trail (𝓝 0):=WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion
  have onSweep:Tendsto (fun z:ℝ×Ratio=>T z.1) sweep (𝓝 0):=ht.comp tendsto_fst
  have ha:Tendsto a sweep (𝓝 0):=WilsonPositionScaleLawCompactIndependent.small Z M H ν d q ht
  obtain ⟨L,hL,step⟩:=WilsonPositionScaleLawCompactKinetic.quantitative Z M H ν F J lead paid d q raw
  obtain ⟨A,hA,move⟩:=WilsonPositionScaleLawPanel.original D
  obtain ⟨B,hB,tail⟩:=WilsonPositionScaleLawCompactPolynomial.original Z M H ν d q
  refine ⟨L*A,L*B,mul_nonneg hL hA,mul_nonneg hL hB,?_⟩
  filter_upwards [step,Metric.tendsto_nhds.mp ha 1 zero_lt_one,Metric.tendsto_nhds.mp onSweep 1 zero_lt_one] with z fin az gz
  let x:=D.purse (fieldsAt F J Z.store d z)
  let y:=D.purse (pre Z M ν d q z.2 (T z.1))
  have htrial:‖a z‖≤1:=by simpa only [dist_zero_right] using az.le
  have hmoney:|T z.1|≤1:=by simpa only [dist_zero_right,Real.norm_eq_abs] using gz.le
  have left:=move (a z) htrial x y
  have right:‖D.itinerary (y,a z)-D.itinerary D.opening‖≤B*|T z.1|^(q+1):=tail z.2 (T z.1) hmoney
  have fee:‖D.itinerary (x,a z)-D.itinerary D.opening‖≤A*‖x-y‖+B*|T z.1|^(q+1):=by
    have three:=dist_triangle (D.itinerary (x,a z)) (D.itinerary (y,a z)) (D.itinerary D.opening)
    rw [dist_eq_norm,dist_eq_norm,dist_eq_norm] at three;exact three.trans (add_le_add left right)
  exact fin.trans ((mul_le_mul_of_nonneg_left fee hL).trans_eq (by change L*(A*‖x-y‖+B*|T z.1|^(q+1))=L*A*‖x-y‖+L*B*|T z.1|^(q+1);ring))

include H lead paid in
theorem qinter (d q:ℕ)(raw:WilsonPositionScaleLawCompactBranch.Raw J d)
    (observed:(measured Z M ν F J d q)=o[sweep] (fun z=>kinetic Z F J z.1^q)):
    (fun z=>exactOp F J Z.store d z-prediction Z M ν F J d q z)=o[sweep] (fun z=>kinetic Z F J z.1^q):=by
  obtain ⟨L,A,hL,hA,bound⟩:=original Z M H ν F J lead paid d q raw
  exact combine (u:=fun z=>exactOp F J Z.store d z-prediction Z M ν F J d q z)
    (g:=fun z:ℝ×Ratio=>kinetic Z F J z.1) q hL hA
    ((WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion).comp tendsto_fst) bound observed

end YM.Integration.WilsonPositionScaleLawCompactQinter
end
