import YM.Integration.WilsonReflectedMixedFundedPortfolio
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSignedConditional
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
variable {p:ℕ}


open WilsonReflectedMixedThermalArms

open Filter Trace.Physical.GermGraph
open scoped Topology



open WilsonReflectedPlacedArm
open WilsonReflectedFundedHearing (Arm cropped)
local notation "X" k:max => Config G ((C).side k p)


open WilsonReflectedFundedHearing (source signed)
open WilsonReflectedOriginalTwoDeposit (raw)
open WilsonReflectedMixedSharpAxis (Cash)

theorem commissioned {ι:Type}[Fintype ι]{d j f K N target:ℕ}{before:j≤f}{up:f≤K}{top:K≤N}
    (admit:Opened C d j p)(ready:(C).ref d≤f){η wage:ℝ}{B:(C).label d≃ₗ[ℂ](C).label d}
    (rows:ι→Arm R d N p f K)(c:ι→ℂ)(o:Site ((C).side f p))(s:Signed)(b:Bool)
    (sites:∀i,(rows i).o=o)(moves:∀i,((rows i).s,(rows i).b)=(s,b))
    (fittedRows:∀i,(rows i).w=B.symm (fitted R d j N p (rows i).Y))
    (cash:WilsonReflectedMixedSharpAxis.Cash (R:=R) d j f K N p target before up top η B (∑i,c i•(rows i).Y) wage):
    ∃A:Arm R d N p f K,A.Y=∑i,c i•(rows i).Y ∧ A.w=∑i,c i•(rows i).w ∧
      A.b=b ∧ A.s=s ∧ A.o=o ∧ A.cash=WilsonMeasuredPublicEntranceGridDebit.bill R d K f A.w ∧
      ∀W,signed R A W=∑i,Motion.scalar (s,b) (c i)*signed R (rows i) W:=by
  obtain ⟨A,born,allocated,hand,turned,pin,price⟩:=WilsonReflectedMixedFundedPortfolio.mounted R cash b s o
  let dated:=(before.trans up).trans top
  let trial:=WilsonReflectedMixedTrialMap.trialMap R admit dated B
  have receipt (Y:(C).label d):trial Y=B.symm (fitted R d j N p Y):=rfl
  have entry:A.w=∑i,c i•(rows i).w:=by
    rw [allocated,←receipt,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,receipt,fittedRows i]
  refine ⟨A,born,entry,hand,turned,pin,price,?_⟩
  intro W
  have report:=WilsonReflectedMixedFundedPortfolio.original R up top ready A rows c
    (fun i=>(sites i).trans pin.symm) (fun i=>(moves i).trans (Prod.ext turned hand).symm) born entry W
  simpa only [turned,hand] using report

/-- The exact signed difference of the entire N-born conditional and the entire
K-born conditional uses all proper incident rows in each native source. -/
theorem original {n N f K t:ℕ}(live:K≤N)(placed:f≤K)(older:t≤K)
    (d k:Fin n→ℕ)(A:(i:Fin n)→Arm R (d i) N p f K)(rows:(i:Fin n)→Fin (k i)→Arm R (d i) N p f K)
    (c:(i:Fin n)→Fin (k i)→ℂ)(sites:∀i j,(rows i j).o=(A i).o)
    (moves:∀i j,((rows i j).s,(rows i j).b)=((A i).s,(A i).b))
    (born:∀i,(A i).Y=∑j,c i j•(rows i j).Y)(funded:∀i,(A i).w=∑j,c i j•(rows i j).w)(W:X t):
    actualTransport C (N:=N) (fun U=>∏i,raw R (source R (A i) (placed.trans live)) U) (older.trans live) W-
      actualTransport C (N:=N) (fun U=>∏i,cropped R (A i) placed U) older W =
      ∑s:(i:Fin n)→Fin (k i),(∏i,Motion.scalar ((A i).s,(A i).b) (c i (s i)))*
        (actualTransport C (N:=N) (fun U=>∏i,raw R (source R (rows i (s i)) (placed.trans live)) U) (older.trans live) W-
           actualTransport C (N:=N) (fun U=>∏i,cropped R (rows i (s i)) placed U) older W):=by
  let weights:=fun (i:Fin n) a=>Motion.scalar ((A i).s,(A i).b) (c i a)
  let fresh:=fun (i:Fin n) (a:Fin (k i))=>raw R (source R (rows i a) (placed.trans live))
  let contact:=fun (s:(i:Fin n)→Fin (k i)) (U:X N)=>∏i,fresh i (s i) U
  have each (U:X N)(i:Fin n):raw R (source R (A i) (placed.trans live)) U=∑a,weights i a*fresh i a U:=
    WilsonReflectedMixedFundedPortfolio.emitted R (placed.trans live) (A i) (rows i) (c i) (sites i) (moves i) (born i) U
  have field:(fun U=>∏i,raw R (source R (A i) (placed.trans live)) U)=
    (fun U=>∑s:(i:Fin n)→Fin (k i),(∏i,weights i (s i))*contact s U):=by
    funext U
    simp_rw [each U]
    exact WilsonReflectedMixedFiniteConditional.product k weights (fun i a=>fresh i a U)
  have paid (s:(i:Fin n)→Fin (k i)):Envelope (contact s):=
    Envelope.prodC Finset.univ _ (fun i _=>Envelope.compactC (WilsonReflectedOriginalTwoDeposit.continuous R _))
  rw [field,WilsonReflectedMixedFiniteConditional.weighted R le_rfl (older.trans live) contact paid,
      WilsonReflectedMixedFiniteConditional.original R live placed older d k A rows c sites moves funded W,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_sub ..).symm

end YM.Integration.WilsonReflectedMixedSignedConditional
end
