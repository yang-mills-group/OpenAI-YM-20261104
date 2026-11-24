import YM.Integration.WilsonReflectedMixedSignedConditional
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedObservedArms
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


structure Printed {d N f K:ℕ}(j:ℕ)(B:(C).label d≃ₗ[ℂ](C).label d)(Y:(C).label d)(s:Signed)(b:Bool)
    (o:Site ((C).side f p))(A:Arm R d N p f K):Prop where
  input:A.Y=Y
  inverse:A.w=B.symm (fitted R d j N p Y)
  hand:A.b=b
  rotation:A.s=s
  site:A.o=o
  cash:A.cash=WilsonMeasuredPublicEntranceGridDebit.bill R d K f A.w

private theorem one {d j f K N q:ℕ}{start:j≤f}{up:f≤K}{top:K≤N}{η bank:ℝ}
    {B:(C).label d≃ₗ[ℂ](C).label d}{Y:(C).label d}
    (paid:WilsonReflectedMixedSharpAxis.Cash (R:=R) d j f K N p q start up top η B Y bank)
    (s:Signed)(b:Bool)(o:Site ((C).side f p)):
    ∃A:Arm R d N p f K,Printed R j B Y s b o A:=by
  obtain ⟨A,hY,hw,hb,hs,ho,hc⟩:=WilsonReflectedMixedFundedPortfolio.mounted R paid b s o
  exact ⟨A,⟨hY,hw,hb,hs,ho,hc⟩⟩

structure Filed {N f K:ℕ}(j d parts:I→ℕ)(axes:(i:I)→(C).label (d i)≃ₗ[ℂ](C).label (d i))
    (Y:(i:I)→Fin (parts i)→(C).label (d i))(c:(i:I)→Fin (parts i)→ℂ)
    (s:I→Signed)(b:I→Bool)(o:I→Site ((C).side f p)) where
  total:(i:I)→Arm R (d i) N p f K
  printed:∀i,Printed R (j i) (axes i) (∑a,c i a•Y i a) (s i) (b i) (o i) (total i)
  basis:(i:I)→Fin (parts i)→Arm R (d i) N p f K
  registered:∀i a,Printed R (j i) (axes i) (Y i a) (s i) (b i) (o i) (basis i a)
  entries:∀i,(total i).w=∑a,c i a•(basis i a).w
  heard:∀i W,signed R (total i) W=∑a,Motion.scalar (s i,b i) (c i a)*signed R (basis i a) W

omit [Fintype I] in
theorem original {N f K:ℕ}(up:f≤K)(top:K≤N)(j d parts:I→ℕ)(start:∀i,j i≤f)
    (opens:∀i,Opened C (d i) (j i) p)(axes:(i:I)→(C).label (d i)≃ₗ[ℂ](C).label (d i))
    (Y:(i:I)→Fin (parts i)→(C).label (d i))(c:(i:I)→Fin (parts i)→ℂ)
    (s:I→Signed)(b:I→Bool)(o:I→Site ((C).side f p)){η:ℝ}{q:ℕ}{wages:(i:I)→Fin (parts i)→ℝ}
    (fees:∀i a,WilsonReflectedMixedSharpAxis.Cash (R:=R) (d i) (j i) f K N p q (start i) up top η (axes i) (Y i a) (wages i a))
    (sold:∀i,WilsonReflectedMixedSharpAxis.Cash (R:=R) (d i) (j i) f K N p q (start i) up top η (axes i)
      (∑a,c i a•Y i a) (∑a,‖c i a‖*wages i a)):
    Nonempty (Filed R (N:=N) (K:=K) j d parts axes Y c s b o):=by
  classical
  choose T printed using fun i=>one R (sold i) (s i) (b i) (o i)
  choose V registered using fun i a=>one R (fees i a) (s i) (b i) (o i)
  have entries i:(T i).w=∑a,c i a•(V i a).w:=by
    let method:=WilsonReflectedMixedTrialMap.trialMap R (opens i) (((start i).trans up).trans top) (axes i)
    have assessed (x:(C).label (d i)):method x=(axes i).symm (fitted R (d i) (j i) N p x):=rfl
    rw [(printed i).inverse,←assessed,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul,assessed,(registered i a).inverse]
  refine ⟨⟨T,printed,V,registered,entries,?_⟩⟩
  intro i W
  have input:(T i).Y=∑a,c i a•(V i a).Y:=by simp_rw [(printed i).input,fun a=>(registered i a).input]
  have opened:=(opens i).post.trans (start i)
  have held:=WilsonReflectedMixedFundedPortfolio.original R up top opened (T i) (V i) (c i)
    (fun a=>(registered i a).site.trans (printed i).site.symm)
    (fun a=>Prod.ext ((registered i a).rotation.trans (printed i).rotation.symm)
      ((registered i a).hand.trans (printed i).hand.symm)) input (entries i) W
  simpa only [(printed i).rotation,(printed i).hand] using held

omit [Fintype I] in
/-- Fixing the funded finite family precedes the choice of face, repeated
selector, earlier date and held group field. -/
theorem read {N f K:ℕ}(top:K≤N)(up:f≤K){j d parts:I→ℕ}{axes:(i:I)→(C).label (d i)≃ₗ[ℂ](C).label (d i)}
    {Y:(i:I)→Fin (parts i)→(C).label (d i)}{c:(i:I)→Fin (parts i)→ℂ}
    {s:I→Signed}{b:I→Bool}{o:I→Site ((C).side f p)}
    (P:Filed R (N:=N) (K:=K) j d parts axes Y c s b o)
    {n:ℕ}(select:Fin n→I){t:ℕ}(earlier:t≤K)(W:X t):
    actualTransport C (N:=N) (fun U=>∏a,raw R (source R (P.total (select a)) (up.trans top)) U) (earlier.trans top) W-
      actualTransport C (N:=N) (fun U=>∏a,cropped R (P.total (select a)) up U) earlier W =
      ∑v:(a:Fin n)→Fin (parts (select a)),(∏a,Motion.scalar (s (select a),b (select a)) (c (select a) (v a)))*
        (actualTransport C (N:=N) (fun U=>∏a,raw R (source R (P.basis (select a) (v a)) (up.trans top)) U) (earlier.trans top) W-
           actualTransport C (N:=N) (fun U=>∏a,cropped R (P.basis (select a) (v a)) up U) earlier W):=by
  have income:=WilsonReflectedMixedSignedConditional.original R top up earlier (fun a=>d (select a)) (fun a=>parts (select a))
    (fun a=>P.total (select a)) (fun a=>P.basis (select a)) (fun a=>c (select a))
    (fun a h=>(P.registered (select a) h).site.trans (P.printed (select a)).site.symm)
    (fun a h=>Prod.ext ((P.registered (select a) h).rotation.trans (P.printed (select a)).rotation.symm)
      ((P.registered (select a) h).hand.trans (P.printed (select a)).hand.symm))
    (fun a=>by simp_rw [(P.printed (select a)).input,fun h=>(P.registered (select a) h).input])
    (fun a=>P.entries (select a)) W
  simpa only [fun a=>(P.printed (select a)).rotation,fun a=>(P.printed (select a)).hand] using income

end YM.Integration.WilsonReflectedMixedObservedArms
end
