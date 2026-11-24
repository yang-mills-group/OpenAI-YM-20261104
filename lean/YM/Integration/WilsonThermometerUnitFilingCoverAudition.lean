import YM.Integration.WilsonThermometerUnitFilingCoverPort

/-! Read every ordered cover derivative on the same finite subroster and auxiliary physical copy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverAudition
open Function Finset Gauge Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Stationary Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open RegulatorIR Prim Profiles Halo WilsonOriginalPaidWalkCover WilsonEmittedRootedJetWage
open WilsonThermometerUnitFilingPinnedIncome WilsonThermometerUnitFilingCoverPieces
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n N:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(s:Finset I)(t:X)(ht:n.val∣N.val)(page:Fin (Pages n N))
local notation "readout"=>WilsonOriginalMixedCoveredRead.field ht (pieces M s) t page (fun _=>True)
local notation "site"=>locus ht page o

theorem smooth:ContDiffAt ℝ ω (readout) 0:=by
  have same:(readout)=fun z=>∑i:↥s, WilsonOriginalSuspendedWord.colored (row ht (M i.val) page) t 0 z:=by
    ext z;simp [WilsonOriginalMixedCoveredRead.field,pieces,WilsonOriginalSuspendedWord.colored,tsum_fintype]
    rfl
  rw [same]
  apply ContDiffAt.sum
  intro i _
  rw [WilsonOriginalSuspendedWord.original]
  apply ContDiffAt.comp
  · have raw:= WilsonOriginalSuspendedWord.smooth (row ht (M i.val) page) 0
    simp only [map_zero]
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ raw)
  exact (WilsonOriginalSuspendedWord.split G N).contDiff.contDiffAt

variable (a:ℂ→L[ℝ]ℝ) {S:Finset Cover} (included:WilsonThermometerUnitFilingCoverChart.Centered N S)
abbrev bank:Portrait G:=WilsonThermometerUnitFilingCoverStock.portrait M s (fun i=>a ((M i).paint t)) 0
abbrev column (G:Gauge)(S:Finset Cover):= ↥(WilsonThermometerUnitFilingCoverChart.patch G S)
local notation "B"=>bank M s t a
local notation "read"=>WilsonThermometerUnitFilingCoverChart.script S (B)
local notation "L"=>WilsonThermometerUnitFilingCoverPort.put included (site) G
local notation "port"=>WilsonThermometerUnitFilingCoverPort.branch included (site) G
local notation "J0"=>column G S

theorem joined (inside:∀ g,LocalOn S ((B) g)):(read)=(a ∘ (readout)) ∘ (L):=by
  funext z
  rw [WilsonThermometerUnitFilingCoverPort.field included (site) (B) inside z]
  exact submitted M s ht page t a.toLinearMap _

theorem paired (inside:∀ g,LocalOn S ((B) g))(k:ℕ)(y:Fin k→Option (J0)):
    WilsonThermometerUnitFilingJointTensor.entry (read) k y=
      (k.factorial:ℝ)⁻¹ *
        a (WilsonOriginalJointDeckMotion.entry k (WilsonThermometerUnitFilingPinnedIncome.envelope ht (pieces M s) page t 0)
            (Option.map (port) ∘ y)):=by
  have sm:=smooth M s t ht page
  have sa:ContDiffAt ℝ ω (a ∘ (readout)) 0:=a.contDiff.contDiffAt.comp _ sm
  rw [WilsonThermometerUnitFilingJointTensor.entry,joined M s t ht page a included inside,
    Next.Foundations.jets_linear (L) (sa.of_le (by simp)),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    a.iteratedFDeriv_comp_left sm (by simp)]
  change (k.factorial:ℝ)⁻¹ * a (iteratedFDeriv ℝ k (readout) 0
    (fun j=>(L) (WilsonThermometerUnitFilingJointTensor.axis (y j))))=_
  apply congrArg ((k.factorial:ℝ)⁻¹ * ·)
  apply congrArg a
  have equal:WilsonThermometerUnitFilingPinnedIncome.envelope ht (pieces M s) page t 0=(readout):=by
    ext z;simp [WilsonThermometerUnitFilingPinnedIncome.envelope]
  rw [equal]
  change iteratedFDeriv ℝ k (readout) 0 _=iteratedFDeriv ℝ k (readout) 0 _
  congr 1;funext i
  exact WilsonThermometerUnitFilingCoverPort.ray included (site) (y i)

end YM.Integration.WilsonThermometerUnitFilingCoverAudition
