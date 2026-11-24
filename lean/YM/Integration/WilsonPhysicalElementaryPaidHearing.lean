import YM.Integration.WilsonPhysicalElementarySourceSpindle
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyPhaseRate
import YM.Integration.WilsonPositionProgramTrialPublicRawTransfer

/-! The actual original N-born elementary detecting fields and their corrected K words are heard together on the earlier flat of N, at a Wilson running power fixed before the physical fit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalElementaryPaidHearing
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
variable (J:ℝ→tower S)(Z:WilsonPrescription G){n D T:ℕ}(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free R.family (d i).val){δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val)
abbrev Axes:Type:=(i:Fin n)→((C₀).labels.level (d i)).Index

def selected {k:ℕ}(a:((C₀).labels.level k).Index):(b:Bool)→Port R k b
  | false=>0
  | true=>a

def heads (a:Axes (R:=R) d)(i:Fin n)(s:{s:ℝ//0<s ∧ s<δ})(mode b:Bool):S.Field (d i).val:=
  WilsonReflectedMixedMasterSchool.field F J Z D T d (fun u=>WilsonPhysicalVaneBasis.field R.family (d u) (a u)) x books i s mode b


theorem named (a:Axes (R:=R) d)(i:Fin n)(s:{s:ℝ//0<s ∧ s<δ})(b:Bool)(N p:ℕ):
    (((books s).rows (d i)).arm b (heads F J Z d x books a i s false b)).source (N,p)=
      source F J Z (d i) (books s) (x i) b (selected (a i) b) N p:=by
  cases b <;> rfl

theorem original [Nonempty (Fin n)](simple:G.Simple)(bliss:Bliss F l arch H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(obeys:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)(h:ℕ)
    (paid:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:Axes (R:=R) d→Fin n→ℝ,∃E:Axes (R:=R) d→Fin n→ℕ,(∀a i,1≤A a i) ∧ ∀p:ℕ,∀ᶠr in trail,
    ∀ρ:Fin n→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer arch h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀(a:Axes (R:=R) d){t u ear K :ℕ}{e E₀:Fin n→ℕ}{tuition:ℝ}{power target:ℕ}
      {wid lo teach}(L:Package R.family wid lo teach)(stop:Stop (C₀) 0 ear u)(window q:ℕ)
      (M:Fin n→ℝ)(one:∀i,1≤M i)(enough:(∑i:↥(Stock.final (Fin n)).val,E a i.val)+2*p≤q),
      School F D T t d e books (heads F J Z d x books a) M E₀ tuition power target ρ f K →
    ∃gate:ℕ,∃up:f<K,∃electrode:(p:ℕ)→(i:Fin n)→Bool→(C₀).label (d i).val ≃ₗ[ℂ] (C₀).label (d i).val,
      ∀N per,∀_live:K≤N,∀b:Fin n→Bool,
      let grade:=fun i=>(d i).val
      let name:=fun i h=>heads F J Z d x books a i (ρ i) false h
      let Y:=fun i=>(((books (ρ i)).rows (d i)).arm (b i) (name i (b i))).source (N,per)
      ∀old:Filed R grade K,let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R grade old (fun p i=>electrode p i (b i))
      file.station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) (b i)) →
      ∀desired requested,2*p≤desired → (∀i,accuracy grade requested i≤e i) → desired+∑i,E₀ i≤requested →
      ∀base j apron reserve first,ReadAt R grade base N per apron requested t reserve power (capital R D tuition) first →
      first≤j → base≤j → ∀height:j+2≤f,K=WilsonInvariantActionPosition.berth R reserve f →
      (∀i,first≤file.station i) → base≤u → ∀past:u≤j,Opened (C₀) 0 u per → Opened (C₀) 0 j per →
      ∀c:ℕ,gate≤c → u+2≤c → c+2≤f → (C₀).S.a c/(C₀).S.a f≤(β f)^window →
      ∀o:Fin n→ Cover,(∀i,8*‖(C₀).S.gridPoint f (o i)‖≤(C₀).S.a (c+1)) →
      (Pairwise fun i k=>2*(C₀).S.a f*(((C₀).path.levels.budget f).B:ℝ)^2≤
        ‖(C₀).S.gridPoint f (o i)-(C₀).S.gridPoint f (o k)‖) →
      let loc:=fun i=>wrap ((C₀).side f per) (o i)
      ∀turn:Fin n→Motion,Ground R N per j f apron loc →
      let road:u≤K:=(past.trans (by omega:j≤f)).trans up.le
      let Q:=submitted R grade (N:=N) file up.le Y turn loc (Stock.final (Fin n))
      let raw:=physical R grade (N:=N) Y turn loc (Stock.final (Fin n))
      ‖actualTransport (C₀) (N:=N) Q road 1-(C₀).omega N per raw‖≤
        ((∏i:↥(Stock.final (Fin n)).val,A a i.val)+(∏i,ceiling (R:=R) (d i).val (M i)))*(wilson arch r)^p :=by
  classical
  choose A E one rate using fun a:Axes (R:=R) d=>WilsonPositionProgramTrialPublicRawTransfer.original F J Z
    simple bliss slow lead obeys D T h d (fun i=>field (C₀) (d i) (a i)) x books paid
  refine ⟨A,E,one,fun p=>?_⟩
  filter_upwards [eventually_all.2 (fun a=>rate a p)] with r tariffs
  intro ρ span left f a t u ear K e E₀ tuition power target wid lo teach L stop window q M own enough campus
  obtain ⟨gate,up,electrode,sold⟩:=WilsonMeasuredPublicEntranceTransferCopyPhaseRate.original F L simple slow
    stop window q (show f=reporter F books ρ from rfl) own campus
  refine ⟨gate,up,electrode,?_⟩
  intro N per live b grade name Y old file station desired requested restored accuracy₀ quota base j apron reserve first read
    firstJ baseJ lower berth stations before past openU openJ c floor cu cf ratio o home apart loc turn ground road Q raw
  have upper:=sold N per live (fun _=>false) b old station desired requested accuracy₀ quota base j apron reserve first
    read firstJ baseJ lower berth stations before past openU openJ c floor cu cf ratio o home apart turn ground
  exact upper.trans (tariffs a ρ span left M own q desired enough restored (fun _=>false) b)

end YM.Integration.WilsonPhysicalElementaryPaidHearing
