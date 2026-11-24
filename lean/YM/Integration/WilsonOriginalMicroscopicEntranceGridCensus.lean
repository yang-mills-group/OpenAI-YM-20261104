import YM.Integration.WilsonOriginalMicroscopicEntranceGridBalance
import YM.Integration.WilsonOriginalMicroscopicEntranceGridReserve
/-! The same three signed stored rows carry their individual dated wages and
are heard jointly before any test or earlier held field is submitted. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceGridCensus
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics
open PhysicalNext OPE.Therm Push.AbsoluteSums.Animals Next.Foundations Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap RG05Readout RG05Readout.Address
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open WilsonOriginalMicroscopicGuardedPage
open WilsonOriginalMicroscopicGuardedPageSchool WilsonAddressedRestartedColumn
open WilsonPositionProgramOriginalBlockedTrial RG05Readout.Records
open scoped Classical Topology BigOperators
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiledPress OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicEntranceGridStock (account Filed)
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (raw guarded gap)
open WilsonOriginalMicroscopicGuardedGridSchool (Placed)
open scoped Classical BigOperators


open WilsonReflectedAffordableArm (charge projectionBill projected)
open WilsonOriginalMicroscopicEntranceGridBalance (coord slotFare)
variable {G:Gauge}(R:Run G)
local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)

def Earned (d N p f:ℕ)(o:Site ((CF).side f p))(z:store CF d p f)(B fee:ℝ):Prop:=
    B≤fee ∧ z.remBound o ((CF).path.rep N p f) (safety CF f) fee ∧
    ((CF).labels.level d).coeffSize z.x≤fee ∧
    ((CF).labels.level d).coeffSize (projection ((CF).labels.level d) (CF).params
      ((CF).path.rep N p f).p.threshold o z)≤fee

theorem refund (d N p f:ℕ)(o:Site ((CF).side f p))(z:store CF d p f)(B fee:ℝ)(pos:0≤B)
    (h:Config G ((CF).side f p)→ℂ)(filed:WilsonAddressedRestartedFiled.Filed R d N p f o h B z)
    (cash:charge R d f*B≤fee):Earned R d N p f o z B fee:=by
  let L:=(CF).path.levels
  have st:0 ≤ stock (CF) f:=zero_le_one.trans (L.params f).columns_ge
  have pr:0≤projectionBill R d f:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have fits {c:ℝ}(bound:c≤charge R d f):c*B≤fee:=(mul_le_mul_of_nonneg_right bound pos).trans cash
  refine ⟨?_,rem_mono filed.paid (fits ?_),filed.primary.trans (fits ?_),filed.measured.trans (fits ?_)⟩
  · simpa only [one_mul] using fits (c:=1) (by unfold WilsonReflectedAffordableArm.charge;linarith only [st,pr])
  · unfold WilsonReflectedAffordableArm.charge;linarith only [pr]
  · unfold WilsonReflectedAffordableArm.charge;linarith only [projected R d f p,st]
  · unfold WilsonReflectedAffordableArm.charge;linarith only [st,pr]

def Qualified (d j:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(CF).label (d a))
    (f n N p:ℕ)(live:f+n≤N)(A:∀a:Fin 3,(CF).label (d a)≃ₗ[ℂ](CF).label (d a))(fees:Fin 3→ℝ):Prop:=
  let fk:f≤f+n:=Nat.le_add_right f n
  let source:=fun a=>Y a (N,p)
  let v:=coord R d j Y A N p
  let B:=slotFare R d f (f+n) v
  ∀o:Fin 3→Site ((CF).side f p),∃Z:∀a:Fin 3,store CF (d a) p f,
    Filed R d (N:=N) (n:=n) source o v B Z ∧ (∀a,Earned R (d a) N p f (o a) (Z a) (B a) (fees a)) ∧
    ∀(s:(J).Mode){u:ℕ}(lower:u≤f)(W:Config G ((CF).side u p)),
      let sites:=pin R fk o
      let upper:=pin R (fk.trans live) o
      let first:=actualTransport (CF) (N:=N) (account R d live source o v Z s) lower W
      read R d source upper live (lower.trans fk) (guarded R d N p (f+n) sites v) s W=first ∧
      read R d source upper live (lower.trans fk) (raw R d N p (f+n) sites v) s W=
        first-units R d (f+n) s*actualTransport (CF) (N:=N) (gap R d N p (f+n) sites v s.val) (lower.trans fk) W

theorem original (d j:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(CF).label (d a)){f n N p:ℕ}(live:f+n≤N)
    (A:∀a:Fin 3,(CF).label (d a)≃ₗ[ℂ](CF).label (d a))(fees:Fin 3→ℝ){h:Fin 3→ℕ}
    (κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)(mature:∀a,(CF).ref (d a)≤f)
    (placed:Placed R d j Y f n N p live A)
    (salary:∀a,charge R (d a) f*(slotFare R d f (f+n) (coord R d j Y A N p) a)≤fees a):
    Qualified R d j Y f n N p live A fees:=by
  unfold Qualified
  intro fk source v B o
  obtain ⟨Z,stamped,seen⟩:=WilsonOriginalMicroscopicEntranceGridBalance.original R d j Y A live o κ pt mature placed
  refine ⟨Z,stamped,?_,seen⟩
  intro a
  have st:0 ≤ stock (CF) (f+n):=zero_le_one.trans (((CF).path.levels.params (f+n)).columns_ge)
  have hp:0≤hike (CF) (f+n) f rate:=Real.rpow_nonneg (div_nonneg ((CF).S.a_pos _).le ((CF).S.a_pos _).le) _
  have bp:0≤B a:=mul_nonneg hp (mul_nonneg (by linarith only [st]) (Work.G08.size_nonneg ..))
  exact refund R (d a) N p f (o a) (Z a) (B a) (fees a) bp _ (stamped a) (salary a)

end YM.Integration.WilsonOriginalMicroscopicEntranceGridCensus
end
