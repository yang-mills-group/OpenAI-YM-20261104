import YM.Integration.WilsonReflectedMixedFiniteBoard
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedFiniteConditional
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

theorem sum {ι:Type}{K t N:ℕ}(live:K≤N)(earlier:t≤K)(s:Finset ι)
    (f:ι→X K→ℂ)(paid:∀i,Envelope (f i))(W:X t):
    actualTransport C (N:=N) (fun U=>∑i∈s,f i U) earlier W=∑i∈s,actualTransport C (N:=N) (f i) earlier W:=by
  classical
  let T:=fun F:X K→ℂ=>actualTransport C (N:=N) F earlier W
  have sub (F H:X K→ℂ)(hF:Envelope F)(hH:Envelope H): T (fun U=>F U-H U)=T F-T H:=
    congrFun (ActualWilsonAbsoluteTransport.sub C R.makes live (ActualWilsonAbsoluteTransport.weighted C R.makes live hF)
      (ActualWilsonAbsoluteTransport.weighted C R.makes live hH) earlier) W
  have add (F H:X K→ℂ)(hF:Envelope F)(hH:Envelope H):T (fun U=>F U+H U)=T F+T H:=by
    have cancel:(fun U=>F U+H U-H U)=F:=by funext U;simp
    have eq:=sub (fun U=>F U+H U) H (hF.addC hH) hH
    rw [cancel] at eq
    exact sub_eq_iff_eq_add.mp eq.symm
  change T (fun U=>∑i∈s,f i U)=∑i∈s,T (f i)
  induction s using Finset.induction_on with
  | empty=>
    simp only [Finset.sum_empty]
    simpa only [sub_self] using sub (fun _=>0) (fun _=>0) (Envelope.constC 0) (Envelope.constC 0)
  | insert b s fresh ih=>
    simp only [Finset.sum_insert fresh]
    rw [add (f b) (fun U=>∑i∈s,f i U) (paid b) (Envelope.sumC s f (fun i _=>paid i)),ih]

/-- The original conditional keeps dependence on the full held configuration;
all the finite uncentered rows use the same positive K vacuum. -/
theorem weighted {ι:Type}[Fintype ι]{K t N:ℕ}(live:K≤N)(earlier:t≤K)
    (f:ι→X K→ℂ)(paid:∀i,Envelope (f i))(c:ι→ℂ)(W:X t):
    actualTransport C (N:=N) (fun U=>∑i,c i*f i U) earlier W=
      ∑i,c i*actualTransport C (N:=N) (f i) earlier W:=by
  rw [sum R live earlier Finset.univ (fun i U=>c i*f i U) (fun i=>(Envelope.constC (c i)).mulC (paid i)) W]
  apply Finset.sum_congr rfl
  intro i _
  exact WilsonReflectedPlacedArm.linear R live earlier (f i) (paid i) (c i) W

theorem product {n:ℕ}(k:Fin n→ℕ)(c f:(i:Fin n)→Fin (k i)→ℂ):
    (∏i,∑j,c i j*f i j)=∑s:(i:Fin n)→Fin (k i),(∏i,c i (s i))*(∏i,f i (s i)):=by
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ,Finset.prod_mul_distrib]

theorem original {n N f K t:ℕ}(live:K≤N)(placed:f≤K)(older:t≤K)
    (d k:Fin n→ℕ)(A:(i:Fin n)→Arm R (d i) N p f K)(rows:(i:Fin n)→Fin (k i)→Arm R (d i) N p f K)
    (c:(i:Fin n)→Fin (k i)→ℂ)(sites:∀i j,(rows i j).o=(A i).o)
    (moves:∀i j,((rows i j).s,(rows i j).b)=((A i).s,(A i).b))
    (funded:∀i,(A i).w=∑j,c i j•(rows i j).w)(W:X t):
    actualTransport C (N:=N) (fun U=>∏i,cropped R (A i) placed U) older W =
      ∑s:(i:Fin n)→Fin (k i),(∏i,Motion.scalar ((A i).s,(A i).b) (c i (s i)))*
        actualTransport C (N:=N) (fun U=>∏i,cropped R (rows i (s i)) placed U) older W:=by
  let weights:=fun (i:Fin n) a=>Motion.scalar ((A i).s,(A i).b) (c i a)
  let branch:=fun (s:(i:Fin n)→Fin (k i)) (U:X K)=>∏i,cropped R (rows i (s i)) placed U
  have each (U:X K)(i:Fin n):cropped R (A i) placed U=∑a,weights i a*cropped R (rows i a) placed U:=
    WilsonReflectedMixedTrialField.field R placed _ _ _ (sites i) (moves i) (funded i) U
  have check:(fun U=>∏i,cropped R (A i) placed U)=
    (fun U=>∑s:(i:Fin n)→Fin (k i),(∏i,weights i (s i))*branch s U):=by
    funext U
    simp_rw [each U]
    exact product k weights (fun i a=>cropped R (rows i a) placed U)
  rw [check]
  apply weighted R live older branch
  intro s
  exact Envelope.prodC Finset.univ _ (fun i _=>WilsonReflectedPlacedArm.trial_paid R ..)

end YM.Integration.WilsonReflectedMixedFiniteConditional
end
