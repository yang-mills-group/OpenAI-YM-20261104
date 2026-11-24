import YM.Integration.WilsonPhysicalFiledPublicRecomposition
import YM.Integration.WilsonPhysicalElementaryMasterHearing
noncomputable section
namespace YM.Integration.WilsonPhysicalEarnedFiledHearing
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
def axis (b:Fin n→Bool)(e:Menu (R:=R) d b (Stock.final (Fin n))):Axes (R:=R) d:=
  fun i=>WilsonPhysicalElementarySourceSpindle.primitive d i (b i) (e ⟨i,Finset.mem_univ _⟩)

private theorem select_primitive (i:Fin n)(b:Bool)(e:Port R (d i) b):
    selected (WilsonPhysicalElementarySourceSpindle.primitive d i b e) b=e:=by
  cases b
  · exact @Subsingleton.elim (Fin 1) inferInstance 0 e
  · rfl

theorem actual (ρ:Fin n→{s:ℝ//0<s ∧ s<δ})(b:Fin n→Bool)(e:Menu (R:=R) d b (Stock.final (Fin n)))
    (N per:ℕ):
    branch F J Z (fun i=>books (ρ i)) d x b (Stock.final (Fin n)) e N per=
      fun i=>source F J Z (d i) (books (ρ i)) (x i) (b i) (selected (axis d b e i) (b i)) N per:=by
  funext i
  simp only [WilsonPhysicalActualMixedFaces.branch,dif_pos (show i∈(Stock.final (Fin n)).val from Finset.mem_univ i)]
  exact congrArg (fun k=>source F J Z (d i) (books (ρ i)) (x i) (b i) k N per)
    (select_primitive (R:=R) d i (b i) _).symm

/-- The original Wilson moment and the older reading of its one filed public word.
All axes and both sales use one program on the same original N-history. -/
theorem original [Nonempty (Fin n)](simple:G.Simple)(bliss:Bliss F l arch H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(obeys:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)(h:ℕ)
    (paid:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:Axes (R:=R) d→Fin n→ℝ,∃E:Axes (R:=R) d→Fin n→ℕ,(∀a i,1≤A a i) ∧ ∀p:ℕ,∀ᶠr in trail,
    ∀ρ:Fin n→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer arch h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀{t u ear K :ℕ}{e E₀:Roster (R:=R) d→ℕ}{tuition:ℝ}{power target:ℕ}
      {wid lo teach}(L:Package R.family wid lo teach)(stop:Stop (C₀) 0 ear u)(window q:ℕ)
      (M:Roster (R:=R) d→ℝ)(one:∀i,1≤M i)(enough:∀a,(∑i:↥(Stock.final (Fin n)).val,E a i.val)+2*p≤q),
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
        ∑z:Menu (R:=R) d b (Stock.final (Fin n)),‖phase F J Z (fun i=>books (ρ i)) d x b turn (Stock.final (Fin n)) z‖ *
          (((∏i:↥(Stock.final (Fin n)).val,A (axis d b z) i.val)+
            (∏i,ceiling (R:=R) (d i).val (M (choice d (axis d b z) i))))*(wilson arch r)^p):=by
  classical
  obtain ⟨A,E,ones,allP⟩:=WilsonPhysicalElementaryMasterHearing.original F J Z d x books simple bliss slow lead obeys h paid
  refine ⟨A,E,ones,fun p=>?_⟩
  filter_upwards [allP p] with r tariff
  intro ρ span left f t u ear K e E₀ tuition power target wid lo teach L stop win q M hM enough campus
  obtain ⟨gate,up,receipt⟩:=tariff ρ span left L stop win q M hM enough campus
  refine ⟨gate,up,?_⟩
  intro N per live b grade Y old st desired requested restored acc quota base j apron reserve first read firstJ baseJ
    lower berth stations before past openU openJ c floor cu cf ratio o home apart loc turn ground road Q raw
  rw [norm_sub_rev]
  apply WilsonPhysicalFiledPublicRecomposition.earned F J Z (fun i=>books (ρ i)) d x b turn
    (Stock.final (Fin n)) up.le live.le road loc 1 old _ (fun i _=>(old.before i).trans live.le)
  · intro z
    have got:=receipt (axis d b z) N per live b old st desired requested restored
      (acc _) (quota _) base j apron reserve first read firstJ baseJ lower berth stations before past openU openJ
      c floor cu cf ratio o home apart turn ground
    rw [actual F J Z d x books ρ b z N per,norm_sub_rev]
    exact got
  · intro i _
    rw [st]
    exact (WilsonReflectedPublicStationFare.original F ((books (ρ i)).rows (d i)) (books (ρ i)).checked
      (b i) (0:S.Field (d i))).1

end YM.Integration.WilsonPhysicalEarnedFiledHearing
