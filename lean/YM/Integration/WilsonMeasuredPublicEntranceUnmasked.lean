import YM.Integration.WilsonMeasuredPublicEntranceHeldDifference
import YM.Integration.WilsonAddressedFiniteGuardEars
import YM.Integration.WilsonOriginalAlternativeTrialSource

/-! The guarded trial and the independent finite word share the exact marked coordinate at the upper site. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceUnmasked
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Labels Source Extra.Histories Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonAddressedFiniteGuardFields (raw guarded cap gap face)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I](d:I→ℕ){N per K:ℕ}
variable (o:I→Site (R.family.side K per))(v:∀i,R.family.label (d i))(z:I→ℂ)
local notation "tuned" => (fun i=>z i • v i)
local notation "C" => R.family
local notation "X" => Config G ((C).side K per)
local notation "P" => (C).path.rep N per K
local notation "program" => WilsonOriginalAlternativeTrialSource.arm R d N per K o v z
local notation "field" => raw R d N per K o tuned
local notation "guard" => guarded R d N per K o tuned

omit [Fintype I][DecidableEq I] in
theorem booked (i:I)(U:X):program i U=guard i U:=by
  change z i*part ((C).localSection (d i)) (o i) (P) U (v i)=part ((C).localSection (d i)) (o i) (P) U (z i • v i)
  rw [LinearMap.map_smul,smul_eq_mul]

omit [Fintype I][DecidableEq I] in
theorem salary (s:Finset I):funded (face program s) ∧ funded (face field s):=by
  have grant:=WilsonAddressedFiniteGuardFields.unary R d N per K o tuned
  constructor
  · apply WilsonSeparatedPrefixCohortUnscale.salary s
    intro i
    refine ⟨?_,cap R d N per K tuned i,?_⟩
    · simpa only [funext (booked R d o v z i)] using (grant i).1
    · intro U;rw [booked R d o v z i U];exact ((grant i).2.2 U).1
  · apply WilsonSeparatedPrefixCohortUnscale.salary s
    intro i
    exact ⟨(grant i).2.1,cap R d N per K tuned i,fun U=>((grant i).2.2 U).2⟩

omit [Fintype I][DecidableEq I] in
theorem charged (s:Finset I)(kn:K≤N){u:ℕ}(uk:u≤K)(W:Config G ((C).side u per)):
    actualTransport (C) (N:=N) (face field s) uk W-actualTransport (C) (N:=N) (face program s) uk W=
      actualTransport (C) (N:=N) (gap R d N per K o tuned s) uk W:=by
  obtain ⟨cropped,entire⟩:=salary R d o v z s
  obtain ⟨B,initial⟩:=cropped.2
  have good:=actualTransport_weighted_integrable (C) R.makes kn cropped.1.aestronglyMeasurable initial (le_refl K)
  rw [actualTransport_base (C) R.makes kn] at good
  have head:Integrable (fun U=>((P).eval U:ℂ)*face program s U) (prior G _):=by
    simpa only [Complex.real_smul] using good
  have paid:=WilsonMeasuredPublicEntranceHeldDifference.withdraw R kn (le_refl K) uk (face field s)
    (face program s) entire head W
  rw [actualTransport_base (C) R.makes kn] at paid
  apply paid.symm.trans
  congr 1
  funext U
  simp only [gap,face,booked R d o v z]

end YM.Integration.WilsonMeasuredPublicEntranceUnmasked
end
