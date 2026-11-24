import YM.Integration.WilsonReceivedChronologicalRosterUnitDepth
import YM.Integration.WilsonReceivedChronologicalRosterSettled

/-! The two-ear receipt uses the original physical sites and their complete digit tape.
Its restriction returns every mixed face to its own signed coordinates in the full filed panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterPhysicalFaces
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonIndependentCollarOrbitalBasisPayment WilsonIndependentCollarPaidWindingPanel
open WilsonOriginalCensusUnitVerse (observed)
open WilsonOriginalCensusUnitLamp (fee)
open WilsonOriginalCensusPositiveSites (Group names part)
open WilsonOriginalCensusPositiveDose (reduced)
open WilsonOriginalCensusUnitDose (enrolled)
open WilsonOriginalCensusFundedUnits (ordinary receipt)
open WilsonReceivedCanonicalVersePortfolio (weight)
open scoped BigOperators Classical

open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonOlderFreshHybridClock (flat)
open WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open WilsonOlderFreshSoftSocketHeard
open WilsonOlderFreshSoftSocketRestored

open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonCoeffUV.Wheel.Mark (mass)
open WilsonOriginalCensusPositiveSites (mapped)
open WilsonOriginalCensusUnitLamp (fee)

open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open Pert.Asymptotics RG LocalComparison
open WilsonReceivedChronologicalRosterOccupiedTurn (product)

open Filter

open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedChronologicalMaterialSites (digits)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalFixedCellFee (tape)
open WilsonOriginalCensusPositiveSites (Group names part)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonCoeffUV.Bank.Mosaic
open WilsonOlderFreshSoftSocketTotal (normalized)

variable {G : Gauge} (R : Run G) {n : ℕ} (k : Fin n → ℕ)
local notation "H" => R.family.path.levels.clock.hatBeta

def pins {per K : ℕ} (site : Fin n → Site (R.family.side K per)) (v c : ℕ) : Fin n → Cover :=
  address R.family.path.levels (digits R site) (c-v) v 0

def terminal (lens : Fin n → ℕ) (pt : Fin n → Chamber) (N per K c v : ℕ)
    (site : Fin n → Site (R.family.side K per)) (x : (i : Fin n) → R.family.label (k i))
    (s : (Stock.census (Fin n)).Mode) (degree : ℕ) : ℂ :=
  normalized R k (fun i=>contact (lens i)) pt N per K c v (digits R site)
    s.val x (pins R site v c) (touch (present lens) s.val) degree (regulatorRun R.family N per v)

def Receipt (lens : Fin n → ℕ) (pt : Fin n → Chamber) (N per K c v u : ℕ)
    (uv : u ≤ v) (vc : v ≤ c) (ck : c ≤ K) (site : Fin n → Site (R.family.side K per))
    (degree power precision : ℕ) (capital : ℝ) : Prop :=
  ∀ x : (i : Fin n) → R.family.label (k i),
    (∀i,(R.family.labels.level (k i)).coeffSize (x i) ≤ capital*(H K)^power) →
    ∀ s : (Stock.census (Fin n)).Mode,
      let word:=product R k (N:=N) x site s
      let result:=terminal R k lens pt N per K c v site x s degree
      let g:=regulatorRun R.family N per v
      (∑q:Selection R k s.val,‖weight R k N per K x s.val q‖) ≤ wallet R k (fun _=>capital) s.val*(H K)^(power*s.val.card) ∧
      ‖actualTransport R.family (N:=N) word ((uv.trans vc).trans ck) 1-result‖ ≤ g^precision ∧
      ‖actualTransport R.family (N:=N) word (vc.trans ck) 1-result‖ ≤ g^precision

private theorem undo {α : Type} {L L' : Levels G} (same : L=L') (cells : Digits L' α) :
    onLevels same (onLevels same.symm cells)=cells:=by cases same; rfl

theorem numbered {P j N per grid first : ℕ}
    {V : Realm G ((WilsonReceivedChronologicalFixedReserve.terms k (fun _=>0) P).order+1) Credit.leanC}
    (draw : V.draws=R.family.path.levels) (lens : Fin n → ℕ) (pt : Fin n → Chamber)
    (fine : grid ≤ j+1+1) (site : Fin n → Site (R.family.side grid per))
    (x : (i : Fin n) → R.family.label (k i)) (s : (Stock.census (Fin n)).Mode) (c degree : ℕ) :
    WilsonIndependentConditionedDenseFilmTerminal.output (R:=R) (d:=k) (P:=P)
      (N:=N) (j:=j) (per:=per) (first:=first) (V:=V) (draw:=draw) (lens:=lens) (pt:=pt)
      (fine:=fine) (site:=site) (votes:=x) (mask:=s) c degree=
    terminal R k lens pt N per (j+1+1) c (first+1) (placed R fine site) x s degree:=by
  unfold WilsonIndependentConditionedDenseFilmTerminal.output terminal pins
  simp only [Nat.sub_self,WilsonReceivedChronologicalMaterialLine.homes,WilsonReceivedChronologicalFixedCellFee.tape,undo]

private theorem projectAddress {m : ℕ} (choose : Fin m → Fin n) (L : Levels G)
    (cells : Digits L (Fin n)) (steps atDate : ℕ) (z : Fin n → Cover) :
    address L (fun a=>cells a∘choose) steps atDate (z∘choose)=(address L cells steps atDate z)∘choose:=by
  induction steps generalizing atDate z with
  | zero => rfl
  | succ steps ih => exact ih (atDate+1) (chartIn (loose L atDate) z (cells atDate))

theorem project {m per K : ℕ} (choose : Fin m → Fin n)
    (site : Fin n → Site (R.family.side K per)) (v c : ℕ) :
    pins R (site∘choose) v c=(pins R site v c)∘choose:=
  projectAddress choose R.family.path.levels (digits R site) (c-v) v 0

theorem original (simple : G.Simple) (travel power precision target : ℕ)
    (enough : target+1+2*power*n ≤ precision) {B : ℝ} (bp : 0≤B) :
    ∀ᶠ v : ℕ in atTop, ∀ {N per f K requested time u c : ℕ} {fk : f≤K} {kn : K≤N},
    0<v → R.family.S.scale K-R.family.S.scale (v-1) ≤ (travel:ℝ)*(1+Real.log (H v)) →
    ∀(uv : u≤v)(vc : v≤c)(ck : c≤K)
      (A : Panel R k N per f K fk kn requested power time B)(file : Filed R k K),
    A.slot=file.station → A.axis=file.A N per →
    ∀(lens : Fin n → ℕ)(pt : Fin n → Chamber)(site : Fin n → Site (R.family.side K per))(degree : ℕ),
      let e:=names k
      Receipt R (k∘e) (lens∘e) (pt∘e) N per K c v u uv vc ck (site∘e) degree power precision B →
      ∀ s : (Stock.census (Fin n)).Mode,
      let x:=votes R k (N:=N) (per:=per) file A.names A.turn
      let word:=product R k (N:=N) x site s
      let result:=terminal R k lens pt N per K c v site x s degree
      (∑q:Selection R k s.val,‖weight R k N per K x s.val q‖) ≤ wallet R k (fun _=>B) s.val*(H K)^(power*s.val.card) ∧
      ‖actualTransport R.family (N:=N) word ((uv.trans vc).trans ck) 1-result‖ ≤ (regulatorRun R.family N per v)^target ∧
      ‖actualTransport R.family (N:=N) word (vc.trans ck) 1-result‖ ≤ (regulatorRun R.family N per v)^target:=by
  filter_upwards [WilsonReceivedChronologicalRosterUnitDepth.original R k simple travel power precision target enough bp] with v restore
  intro N per f K requested time u c fk kn vp span uv vc ck A file station axes lens pt site degree e earned s x word result
  have wage:=WilsonOriginalObservedRoseFittedPurse.column R k A file station axes
  obtain ⟨_,low,higher⟩:=earned (fun i=>x (e i)) (fun i=>wage (e i)) (part k s)
  dsimp only [terminal] at low higher
  rw [project R e site v c] at low higher
  refine ⟨WilsonReceivedChronologicalFixedRoseFittedBank.original R k A file station axes s,?_,?_⟩
  · exact restore vp span A file station axes lens pt vc ck (digits R site) (pins R site v c) degree
      (regulatorRun R.family N per v) site ((uv.trans vc).trans ck) 1 s low
  · exact restore vp span A file station axes lens pt vc ck (digits R site) (pins R site v c) degree
      (regulatorRun R.family N per v) site (vc.trans ck) 1 s higher

end YM.Integration.WilsonReceivedChronologicalRosterPhysicalFaces
