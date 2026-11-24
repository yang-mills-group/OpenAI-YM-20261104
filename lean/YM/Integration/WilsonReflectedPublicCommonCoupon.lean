import YM.Integration.WilsonReflectedPublicPairedStocks
import YM.Integration.WilsonReflectedPublicCommonRows
import YM.Integration.WilsonReflectedPublicDoseField

/-! The double reservation for the two genuinely landed public arms, on the same registered estate. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCommonCoupon
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonReflectedOpticalArm WilsonReflectedFullPanel WilsonReflectedFundedHearing
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedRestoredStation
open scoped Topology Classical
variable {G:Gauge} {R:Run G} {order:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family order S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "lev" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

open Extra.Histories.Motion RG05Readout.Address MergeProof Push.Local
open WilsonReflectedFundedHearing WilsonReflectedFullPanel WilsonReflectedAffordableArm
open WilsonReflectedPublicPairedStocks WilsonReflectedPublicCommonDose
open WilsonReflectedPublicGuardedColumns WilsonReflectedFundedHearing

def Earned {N p f K d:ℕ}(q:ℕ)(C:ℝ)(Y:(C₀).label d)(pay:ℝ)(j:ℕ)
    (M:(C₀).label d ≃ₗ[ℂ] (C₀).label d)(s:Motion)(o:Site ((C₀).side f p))
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)(h:f<K)(top:K ≤ N):Prop :=
  let y:=offer R Y est (h.le.trans top)
  let χ:=WilsonThermometerMarchSource.charge y
  let c:=dose χ C pay
  let data:=((c*χ:ℝ):ℂ) • reduce y
  let wage:=WilsonReflectedPublicMountedInvoice.wage R f
  let Ω:=orbitCost ((C₀).labels.level d)
  ∃A:Arm R d N p f K,A.Y=Y ∧ A.w=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y) ∧
    A.b=s.2 ∧ A.s=s.1 ∧ A.o=o ∧ (∃L:Arm R d N p K K,WilsonReflectedRestoredStation.Situated R h.le A L) ∧
    ∃X E, Joined R A h.le top (c:ℂ) (marked R (N:=N) 0 s o V u data f)
      wage (Ω*(1+wage)) ((2+Ω)*((β f)^q)⁻¹) X E

theorem original {N p f K d:ℕ}{X:Type}(t T q jets:ℕ)(C:ℝ)
    (book:Bool → X → (C₀).label d)(fee:Bool → X → ℝ)(date:Bool → ℕ)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)
    (M:Bool → (C₀).label d ≃ₗ[ℂ] (C₀).label d)(h:f<K)(start:∀b,date b ≤ f)(top:K ≤ N)
    (stock:Inventory (R:=R) t T book fee V u est (h.le.trans top))
    (trade:Stock (R:=R) (p:=p) q jets C book fee date M h start top)
    (b:Bool)(v:X)(s:Motion)(o:Site ((C₀).side f p))
    (heard:∀L,(marked R (N:=N) 0 s o V u (reduce (offer R (book b v) est (h.le.trans top))) f).1 L=
      ((WilsonThermometerMarchSource.charge (offer R (book b v) est (h.le.trans top)):ℝ):ℂ)⁻¹ *
        (((C₀).path.rep N p f).eval L:ℂ)*WilsonReflectedOriginalTwoDeposit.held R
          (WilsonReflectedPlacedArm.original R d (h.le.trans top) (book b v) s.2 s.1 o) f L):
    receipt R d (date b) K N p jets ((start b).trans h.le) top (1/32) (M b) (book b v) (mesh (date b)^d*fee b v) ∧
    Earned (R:=R) q C (book b v) (fee b v) (date b) (M b) s o V u est h top:=by
  obtain ⟨ticket,arms⟩:=trade b v
  obtain ⟨A,src,weight,flip,turn,site,_,placed,sale⟩:=arms s.2 s.1 o
  refine ⟨ticket,?_⟩
  unfold Earned
  intro y χ c data wage Ω
  let a:ℝ:=(2+Ω)*((β f)^q)⁻¹
  have ap:0 ≤ a:=mul_nonneg (by linarith only [orbitCost_one_le ((C₀).labels.level d)])
    (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans ((lev).fits.delayed f).le) _))
  obtain ⟨E,unit⟩:=sale 1 (by simp)
  have reorder:(2+Ω)*C*((β f)^q)⁻¹*fee b v=a*C*fee b v:=by dsimp only [a];ring
  rw [reorder] at unit
  obtain ⟨X₀,form,size,paid,reg,forced,field⟩:=stock.1 b v s o
  have sameSource:WilsonReflectedFundedHearing.source R A (h.le.trans top)=
      WilsonReflectedPlacedArm.original R d (h.le.trans top) (book b v) s.2 s.1 o:=by
    unfold WilsonReflectedFundedHearing.source
    rw [src,flip,turn,site]
  let old:=marked R (N:=N) 0 s o V u (reduce y) f
  let θ:ℂ:=(c*χ:ℝ)
  refine ⟨A,src,weight,flip,turn,site,placed,stretch θ X₀,stretch (c:ℂ) E,?_⟩
  have raw:=WilsonReflectedPublicCommonRows.original R A h.le top χ C (fee b v) a (le_max_left ..) ap
    old wage (Ω*(1+wage)) X₀ E (site.symm ▸ form) size (site.symm ▸ paid) (site.symm ▸ reg) forced
    (site.symm ▸ field) (fun U=>by rw [sameSource];exact heard U) unit
  have mounted:=WilsonReflectedPublicDoseField.marked_real R (N:=N) 0 s o V u (reduce y) (c*χ) f
  rw [show marked R (N:=N) 0 s o V u data f=θ • old from mounted]
  exact raw

end YM.Integration.WilsonReflectedPublicCommonCoupon
end
