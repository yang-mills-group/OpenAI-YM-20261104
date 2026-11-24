import YM.Integration.WilsonPhysicalEarnedFiledHearing
import YM.Integration.WilsonPhysicalHomeSourceCosts

/-! The public two-home hearings use every actual elementary column on one shared Born assignment. Their total physical charge is independent of the two genuine home radii, the period, and the ultraviolet cutoff. -/
noncomputable section
namespace YM.Integration.WilsonPhysicalTwoHomeOpticalCash
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells
open Extra.Histories PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonReflectedPublicOrientedFaces (displayed)
open OPE Next.Rank Overlay Bid Push.GridApprox MergeProof Ribbons Accent ManyCopies
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted physical)
open WilsonMeasuredPublicEntranceOrderedPins (Release publicValue)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open Table Climb Next.UVStress
open Extraction Spec PertExtension PertExtension.LatticePT Trace.Pilot Trace.Terrace
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open scoped Classical BigOperators Topology
open Trace.Physical.GermGraph (Opened)
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
variable {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}
local notation "C₀" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntranceTransferKnotBoard (At)
open RG16 RG16.Literal PhysicalNext.Repeat.Mallow Bandage



open RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register
open WilsonAddressedHomeDose (ceiling)
open WilsonPhysicalActualMixedMenus (Port source)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPhysicalVaneBasis (field)
open WilsonPhysicalElementaryPaidHearing (Axes selected heads)
open WilsonPhysicalElementaryMasterCampus (master choice)
open WilsonPhysicalElementarySourceSpindle (Roster)
variable (J:ℝ→tower S)(Z:WilsonPrescription G){n D T:ℕ}(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free R.family (d i).val){δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val)

open WilsonPhysicalActualMixedFaces (Menu phase names branch)
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallBounded (cost)
open WilsonPhysicalEarnedFiledHearing (axis)

theorem room (simple:G.Simple)(bliss:Bliss F l arch H):
    ∀ᶠr in trail,0≤wilson arch r ∧ 2*r≤outer arch 1 r:=by
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [link.positive,(link.conforms simple).eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    self_mem_nhdsWithin] with r gp half (rp:0<r)
  have inv₂:(2:ℝ)≤(wilson arch r)⁻¹:=by
    rw [inv_eq_one_div,le_div_iff₀ gp]
    linarith only [half]
  exact ⟨gp.le,by simpa only [outer,pow_one,mul_comm r] using mul_le_mul_of_nonneg_right inv₂ rp.le⟩

private def panelBill (A:Axes (R:=R) d→Fin n→ℝ)(M:Roster (R:=R) d→ℝ)(a:Axes (R:=R) d):ℝ:=
  (∏i:↥(Stock.final (Fin n)).val,A a i.val)+(∏i,ceiling (R:=R) (d i).val (M (choice d a i)))

private theorem fare (A:Axes (R:=R) d→Fin n→ℝ)(M:Roster (R:=R) d→ℝ)(a:Axes (R:=R) d):
    panelBill d A M a≤∑k,|panelBill d A M k|:=
  (le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (panelBill d A M j)) (Finset.mem_univ a))

theorem original [Nonempty (Fin n)](simple:G.Simple)(bliss:Bliss F l arch H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(obeys:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (birth:Assignment F J H l simple)
    (shared:∀s,∃cap:D≤(birth.day s.val).1,Shared F (books s) (trim cap (birth.day s.val).2))
    (M:Roster (R:=R) d→ℝ)(one:∀i,1≤M i)
    (paid:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃W:ℝ,∃E:Axes (R:=R) d→Fin n→ℕ,0≤W ∧ ∀p:ℕ,∀ᶠr in trail,
    ∀ρ:Fin n→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤2*r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀{t u ear K :ℕ}{e E₀:Roster (R:=R) d→ℕ}{tuition:ℝ}{power target:ℕ}
      {wid lo teach}(L:Package R.family wid lo teach)(stop:Stop (C₀) 0 ear u)(window q:ℕ)
      (enough:∀a,(∑i:↥(Stock.final (Fin n)).val,E a i.val)+2*p≤q),
      School F D T t (fun w:Roster (R:=R) d=>d w.1) e books (master F J Z d x books) M E₀
        tuition power target (fun w=>ρ w.1) (reporter F books (fun w:Roster (R:=R) d=>ρ w.1)) K →
    ∃gate:ℕ,∃up:f<K,∀N per:ℕ,∀_live:K<N,∀b:Fin n→Bool,
      let grade:=fun i=>(d i).val
      let Y:=names F J Z (fun i=>books (ρ i)) d x b N per
      ∀old:Filed R grade K,
      old.station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) (b i)) →
      ∀desired requested,2*p≤desired → (∀a i,accuracy grade requested i≤e (choice d a i)) →
        (∀a,desired+∑i,E₀ (choice d a i)≤requested) →
      ∀base j apron reserve first,ReadAt R grade base N per apron requested t reserve power (capital R D tuition) first →
      first≤j → base≤j → ∀height:j+2≤f,K=WilsonInvariantActionPosition.berth R reserve f →
      (∀i,first≤old.station i) → base≤u → ∀past:u≤j,Opened (C₀) 0 u per → Opened (C₀) 0 j per →
      ∀c:ℕ,gate≤c → u+2≤c → c+2≤f → (C₀).S.a c/(C₀).S.a f≤(β f)^window →
      ∀o:Fin n→ Cover,(∀i,8*‖(C₀).S.gridPoint f (o i)‖≤(C₀).S.a (c+1)) →
      (Pairwise fun i k=>2*(C₀).S.a f*(((C₀).path.levels.budget f).B:ℝ)^2≤
        ‖(C₀).S.gridPoint f (o i)-(C₀).S.gridPoint f (o k)‖) →
      let loc:=fun i=>wrap ((C₀).side f per) (o i)
      ∀turn:Fin n→Motion,Ground R N per j f apron loc →
      let road:u≤K:=(past.trans (by omega:j≤f)).trans up.le
      let Q:=submitted R grade (N:=N) old up.le Y turn loc (Stock.final (Fin n))
      let raw:=physical R grade (N:=N) Y turn loc (Stock.final (Fin n))
      ‖actualTransport (C₀) (N:=N) Q road 1-(C₀).omega N per raw‖≤
W*(wilson arch r)^p:=by
  classical
  obtain ⟨A,E,_ones,allP⟩:=WilsonPhysicalEarnedFiledHearing.original F J Z d x books simple bliss slow lead obeys 1 paid
  obtain ⟨B,nonneg,variation⟩:=WilsonPhysicalHomeSourceCosts.original F J simple birth books shared Z lead obeys bliss d 1
  let cap:=∏i:↥(Stock.final (Fin n)).val,max 1 (B i*cost (C₀) (x i))
  let wallet:=∑a:Axes (R:=R) d,|panelBill d A M a|
  have cap₀:0≤cap:=Finset.prod_nonneg fun _ _=>zero_le_one.trans (le_max_left ..)
  have wall₀:0≤wallet:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  refine ⟨cap*wallet,E,mul_nonneg cap₀ wall₀,fun p=>?_⟩
  filter_upwards [allP p,variation,room F simple bliss] with r earned variation aperture
  intro ρ span left f t u ear K e E₀ tuition power target wid lo teach L stop win q enough campus
  have whereAt:∀i,r≤(ρ i).val ∧ (ρ i).val≤outer arch 1 r:=fun i=>⟨(span i).1,(span i).2.trans aperture.2⟩
  obtain ⟨gate,up,receipt⟩:=earned ρ whereAt left L stop win q M one enough campus
  refine ⟨gate,up,?_⟩
  intro N per live b grade Y old st desired requested restored acc quota base j apron reserve first read firstJ baseJ
    lower berth stations before past openU openJ c floor cu cf ratio o home apart loc turn ground road Q raw
  apply (receipt N per live b old st desired requested restored acc quota base j apron reserve first read firstJ baseJ
    lower berth stations before past openU openJ c floor cu cf ratio o home apart turn ground).trans
  let w:=fun z:Menu (R:=R) d b (Stock.final (Fin n))=>‖phase F J Z (fun i=>books (ρ i)) d x b turn (Stock.final (Fin n)) z‖
  have bound:(∑z,w z)≤cap:=(variation ρ (fun i=>(whereAt i).2) x b turn (Stock.final (Fin n))).trans (by
    apply Finset.prod_le_prod
    · intro i _
      split
      · exact mul_nonneg (nonneg i) (Finset.sum_nonneg fun _ _=>norm_nonneg _)
      · exact zero_le_one
    · intro i _
      split
      · exact le_max_right ..
      · exact le_max_left ..)
  have gp:=pow_nonneg aperture.1 p
  calc
    _≤∑z,w z*(wallet*(wilson arch r)^p):=Finset.sum_le_sum fun z _=>mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (fare d A M (axis d b z)) gp) (norm_nonneg _)
    _=(∑z,w z)*(wallet*(wilson arch r)^p):=(Finset.sum_mul ..).symm
    _≤cap*(wallet*(wilson arch r)^p):=mul_le_mul_of_nonneg_right bound (mul_nonneg wall₀ gp)
    _=_:=(mul_assoc ..).symm

end YM.Integration.WilsonPhysicalTwoHomeOpticalCash
