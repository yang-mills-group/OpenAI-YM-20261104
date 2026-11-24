import YM.Integration.WilsonOriginalMicroscopicEntranceDoseColumns
import YM.Integration.WilsonReflectedPublicCommonEstate

/-! On the already selected public board, issue the three native arms, the input fees, and the exact common-dose lower fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDoseElected
open Function Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Push Push.Local Marker Motion
open PhysicalNext PhysicalNext.Repeat.Legato Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi
open RG05Readout RG05Readout.Address WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder
open WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField WilsonThermometerMarchSource
open WilsonThermometerReflectedTrajectory WilsonAddressedAlignedColumn WilsonReflectedFundedHearing
open WilsonReflectedPublicGuardedColumns WilsonOriginalMicroscopicEntranceDoseBoard WilsonReflectedOpticalArm
open Extra.Histories.Relay
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){d:Fin 3→ℕ}{N per f t K:ℕ}{o:Fin 3→Site (R.family.side f per)}
  (B:Board R d N per f o t)

variable (C pay:Fin 3→ℝ)

def dose (i:Fin 3):ℝ:=
  WilsonReflectedPublicCommonDose.dose (charge (offer R (B.x i) (B.home i) B.live.le)) (C i) (pay i)

local notation "c" => dose R B C pay
local notation "mesh" => R.family.S.a
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

theorem original (dates rate power:Fin 3→ℕ)(cap:Fin 3→ℝ)
    (M:∀i,R.family.label (d i) ≃ₗ[ℂ] R.family.label (d i))(fk:f<K)(kn:K≤N)
    (paid:∀i,WilsonReflectedPublicCommonEstate.Ready (R:=R) (rate i) (cap i) (power i) (C i)
      (B.x i) (dates i) (pay i) (M i) (B.sight i) (B.frames i) (B.home i) fk kn (B.motion i) (o i)):
    ∃A:∀i,Arm R (d i) N per f K,∃Q E:∀i,Coefficient (R.family.labels.level (d i)) (R.family.side f per),
      (∀i,(A i).Y=B.x i ∧ (A i).w=(M i).symm (WilsonOriginalMicroscopicGuardedPage.full R (d i) N per (dates i) (B.x i)) ∧
        (A i).b=(B.motion i).2 ∧ (A i).s=(B.motion i).1 ∧ (A i).o=o i ∧
        (∃upper:Arm R (d i) N per K K,WilsonReflectedRestoredStation.Situated R fk.le (A i) upper) ∧
        WilsonReflectedPublicGuardedColumns.Joined R (A i) fk.le kn (c i:ℂ) (WilsonOriginalMicroscopicEntranceDoseColumns.row R B c i)
          (WilsonReflectedPublicMountedInvoice.wage R f)
          (orbitCost (R.family.labels.level (d i))*(1+WilsonReflectedPublicMountedInvoice.wage R f))
          ((2+orbitCost (R.family.labels.level (d i)))*((H f)^(rate i))⁻¹) (Q i) (E i) ∧
        (R.family.labels.level (d i)).coeffSize
          (((c i:ℂ)*(((mesh K:ℂ)^(d i))⁻¹)) • WilsonReflectedPublicGuardedMotion.coords R (A i))≤cap i*(H K)^(power i)) ∧
      ∀s:(Stock.census (Fin 3)).Mode,∀U:Config G (R.family.side f per),
        (∏i∈s.val,(Q i).exponentialEntry (A i).o (R.family.localSection (d i)) (R.family.path.rep N per f) U)=
          head R B (fun i=>(c i:ℂ)) s U:=by
  classical
  choose A names wages b spin home seated Q E postings limits using paid
  refine ⟨A,Q,E,fun i=>⟨names i,wages i,b i,spin i,home i,seated i,postings i,limits i⟩,?_⟩
  exact WilsonOriginalMicroscopicEntranceDoseColumns.original R B A fk.le kn c Q E postings
end YM.Integration.WilsonOriginalMicroscopicEntranceDoseElected
end
