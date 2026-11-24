import YM.Integration.WilsonReflectedPublicGuardedMotion
/-! Each complete and proper face of the independently localized reflected trial
is literally a funded native K-birth on its already evolved physical vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicTrialRoster
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Marker
open Push PhysicalNext.Repeat.Legato WilsonReflectedFundedHearing
open QuadraticLocal.Affinity
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p f K:ℕ}{I:Type} [Fintype I][DecidableEq I]
    (d:I→ℕ)(A:(i:I)→Arm R (d i) N p f K)(h:f≤K)(dose:I→ℂ)
local notation "C₀" => R.family
local notation "D₀" => WilsonOriginalAlternativeFiniteSource.disks (V:=I)
local notation "P₀" => (C₀).path.rep N p K

variable (N p K) in
def factor (i:I):ℂ:=dose i*(((C₀).S.a K:ℂ)^(d i))⁻¹

def root (i:I):= ((C₀).S.toDepth h p).embed (A i).o

def weight (i:I): (C₀).label (d i):=WilsonReflectedPublicGuardedMotion.coords R (A i)

omit [Fintype I][DecidableEq I] in
theorem original (i:I)(U:Config G ((C₀).side K p)):
    WilsonOriginalAlternativeTrialSource.arm R d N p K (root R d A h) (weight R d A)
      (factor R K d dose) i U=dose i*cropped R (A i) h U:=by
  dsimp only [WilsonOriginalAlternativeTrialSource.arm,root,weight,factor]
  rw [WilsonReflectedPublicGuardedMotion.placed]
  ring

theorem complete (x:Wallet D₀)(s:(Stock.census I).Mode)(U:Config G ((C₀).side K p)):
    (WilsonOriginalAlternativeTrialSource.source R d N p K (root R d A h) (weight R d A)
        (factor R K d dose) x U).part s = ((P₀).eval U:ℂ) *
      ∏i∈s.val,(x i).val*(dose i*cropped R (A i) h U):=by
  rw [WilsonOriginalAlternativeTrialSource.part]
  simp only [WilsonOriginalAlternativeTrialSource.mode,original,Complex.real_smul]

end YM.Integration.WilsonReflectedPublicTrialRoster
end
