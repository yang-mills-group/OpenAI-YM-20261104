import YM.Integration.WilsonMeasuredPublicEntranceTransferElectedFees

/-! The signed four-corner source income at its issued optical date, before
identifying a measured coupling. The same bound applies to repeated labels,
the scalar and the two genuinely different branches of each public name. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicRawFare
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register Pert.Asymptotics
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
local notation "C₀" => R.family
local notation "β" => (C₀).path.levels.clock.hatBeta

theorem original {I:Type}[Fintype I][Nonempty I](simple:G.Simple)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F J)
    (obeys:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator (C₀).book).Field (d i).val)
    (x:∀i,RG17.Free C₀ (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (admit:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:I→ℝ,∃E:I→ℕ,(∀i,1≤A i) ∧ ∀ᶠr in trail,
      ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∀(i:I)(mode arm:Bool),
        let v:=WilsonReflectedMixedMasterSchool.field F J Z D T d y x books i (ρ i) mode arm
        Motion.orbitCost ((C₀).labels.level (d i).val)*charge F ((books (ρ i)).rows (d i)) f arm v≤
          A i*(β f)^(E i):=by
  classical
  obtain ⟨An,En,n₀,hn⟩:=WilsonAddressedMixedNamedIncome.original F J Z simple bliss slow lead obeys D T h d y x books
  obtain ⟨Ah,Eh,h₀,hh⟩:=WilsonMovingForkHomeIncome.original F J Z simple bliss slow lead obeys D T h d x books admit
  let O(i:I):=Motion.orbitCost ((C₀).labels.level (d i).val)
  have op(i:I):1≤O i:=Motion.orbitCost_one_le _
  have mn(i:I):1 ≤ max (An i) (Ah i):=(n₀ i).trans (le_max_left ..)
  refine ⟨fun i=>O i*max (An i) (Ah i),fun i=>max (En i) (Eh i),
    fun i=>one_le_mul_of_one_le_of_one_le (op i) (mn i),?_⟩
  filter_upwards [hn,hh] with r named home
  intro ρ span near f i mode arm v
  have bp:1≤β f:=((C₀).path.levels.fits.delayed f).le
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (op i))
  cases mode
  · exact (named ρ span near (fun _=>arm) i).2.2.trans
      (mul_le_mul (le_max_left ..) (pow_le_pow_right₀ bp (le_max_left ..))
        (pow_nonneg (zero_le_one.trans bp) _) (zero_le_one.trans (mn i)))
  · exact (home ρ span near (fun _=>arm) i).2.2.trans
      (mul_le_mul (le_max_right ..) (pow_le_pow_right₀ bp (le_max_right ..))
        (pow_nonneg (zero_le_one.trans bp) _) (zero_le_one.trans (mn i)))

end YM.Integration.WilsonPositionProgramTrialPublicRawFare
end
