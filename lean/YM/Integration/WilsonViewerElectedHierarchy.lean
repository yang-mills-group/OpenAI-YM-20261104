import YM.Integration.WilsonViewerOriginalProducts
import YM.Integration.WilsonOriginalSeparatedElection

/-! The sharp physical reader, the position calibration, the ordered extraction
and the all-viewer signed consumers share an original Wilson election. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonMSDictionaryVector WilsonPositionHomogeneousFrame
open WilsonPositionSeparatedProfileMatching WilsonMacroscopicDetector
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin} {J : ℝ → PhysMS.tower S}
    {Y : (Bel R.family.book).Hierarchy} {A : Trace.Terrace.Arch R.family}
    {ℓ : Ultrafilter (ℕ × ℕ)} {cohort : Ultrafilter (ℕ × ℕ) → Prop}
    {simple : G.Simple}

structure Selected (F : Final R.family f S) (L : EveryPhase.Almanac F)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → PhysMS.tower S)
    (Y : (Bel R.family.book).Hierarchy) (A : Trace.Terrace.Arch R.family)
    (ℓ : Ultrafilter (ℕ × ℕ)) (simple : G.Simple) (cohort : Ultrafilter (ℕ × ℕ) → Prop) : Prop where
  phases : EveryPhase.Completed F L
  trace : Trace.Target.Result.{u} F simple
  exclusion : Trace.Target.Exclusion.{u} F
  facilities : Facilities R.family f S
  foundation : Foundation F Q
  sharp : SingleLog F Q.port
  bliss : Bliss F ℓ A Y
  original : (ℓ : Filter (ℕ × ℕ)) ≤ f.fuse
  retained : cohort ℓ
  matrix : MatrixTicket (C:=R.family) S F.sector.derivatives (ℓ : Filter (ℕ × ℕ))
  leading : Leading F J
  obeys : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d
  calibration : ∃ (T T' : ℝ → Spin.change S 4) (φ : E4 → ℝ) (a d e : ℝ → ℝ),
    (∀ᶠ r in trail, J r 4 = T' r) ∧
    Trace.Target.XScheme F simple Y ℓ T T' φ ∧ Trace.Target.FieldComparison F Y A T T' a d e

def OnRun (R : Run G) (simple : G.Simple) (cohort : Ultrafilter (ℕ × ℕ) → Prop) : Prop :=
  ∀ f : Extraction.Order, ∃ (w : Extraction.Order) (S : Table R.family.book)
    (F : Final R.family (f.refine w) S) (L : EveryPhase.Almanac F)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → PhysMS.tower S)
    (Y : (Bel R.family.book).Hierarchy) (A : Trace.Terrace.Arch R.family) (ℓ : Ultrafilter (ℕ × ℕ)),
    Selected.{u} F L Q J Y A ℓ simple cohort

theorem on_elected (given : WilsonMacroscopicFundedReader.Elected.{u} R simple cohort) :
    OnRun.{u} R simple cohort := by
  intro f
  obtain ⟨w,S,F,L,Q,done,trace,exclusion,fac,base,sharp,Y,A,ℓ,bliss,T,T',J,φ,a,d,e,
    grade,scheme,comparison,leading,obeys,under,retained,ticket⟩ := given f
  exact ⟨w,S,F,L,Q,J,Y,A,ℓ,done,trace,exclusion,fac,base,sharp,bliss,under,retained,
    ticket,leading,obeys,T,T',φ,a,d,e,grade,scheme,comparison⟩

section Election
open Lattice Wilson RG RG.Supply Pressure Input Org Precision PhysicalNext PhysicalNext.Repeat
open Push.PriceCompiler ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase WilsonWindowBookPurchase
open MSbar.Heath OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonMarkedIndependentPhysicalIntake WilsonVacuumPreResetFiniteHeatScale
open WilsonVacuumPreResetFiniteHeatTable
variable {φ : ℕ → ℕ}

/-- Keep the predeclared forecasts, original support exponent and quiet hierarchy
when producing the reader. Every subsequent signed test uses this selection. -/
theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap)
    (simple : G.Simple) {ε ξ : ℝ} (positive : 0 < ε) (finance : Glacier (a:=a) simple ξ)
    (law : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted law s (ThroughLaunch.raging s q))
    (bills : ℕ → ℕ → Gear G → ℝ) (extra : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonReportingAbsoluteInletSchool.OnRun.{u} cap simple ε law U
        (@WilsonOriginalSeparatedElection.demands G φ simple law split U bills (@extra)) R T W ∧
      WilsonPositionProgramNestedElection.course simple a ξ R.kit ∧ R2I.RG05Joint.AcrossPanels R.kit ∧
      (∀ i, (R.family.path.levels.budget i).supportExponent = 100) ∧ WilsonOriginalSeparatedElection.Quiet R ∧
      ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        OnRun.{u} R simple cohort := by
  obtain ⟨R,T,W,source,elected,panels,strip,quiet,viewers⟩ :=
    WilsonOriginalSeparatedElection.original.{u} a cap U mono simple positive finance law split permitted bills (@extra) paid
  exact ⟨R,T,W,source,elected,panels,strip,quiet,fun cohort grant => on_elected (viewers cohort grant)⟩
end Election

variable (run : Selected.{u} F L Q J Y A ℓ simple cohort)
    (Z : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "P" => homogeneous F J Z
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
variable {n : ℕ}
include run in
theorem Selected.correlations (ν : ℝ) (d : ℕ) (ψ : Test n) (v : Fin n → Sec G d)
    (q : ℕ) (g : ℝ → ℝ) (coupling : Coupling G g)
    (clock : ∃ K : ℝ, 0<K ∧ ∀ᶠ r in trail, g r ≤ K*|θ r|)
    (signed : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail,
      ‖observed Z F J none d ψ v r - polynomial Z M ν d ψ v q (θ r)‖ ≤ ε*|θ r|^q) :
    matchesThrough Z M F J ν d ψ v q := by
  obtain ⟨_,_,X,_,_,_⟩ := run.bliss.picks (fun i : ℕ => 1/((i:ℝ)+1))
    tendsto_one_div_add_atTop_nhds_zero_nat (fun i => by positivity)
  exact WilsonViewerSignedDictionary.correlations F Q J Z M simple run.leading run.obeys X
    run.foundation ν d ψ v q g coupling clock signed

variable {σ : Prescription (Press.portDeck G)} {branch : Bool}
    (matchMS : Main.Match Z simple M σ branch) (ν : ℝ) (d : Fin n → ℕ)
    (v : (i : Fin n) → RG17.Free R.family (d i)) (h q : ℕ) (g : ℝ → ℝ)
    {E : Type} [Fintype E] {e : E → ℕ} (w : Labels S e) {δ : ℝ} (clearance : 0 < δ)
local notation "inputs" => fun r i => P r (d i) (v i)

include run clearance in
theorem Selected.ordinary (ψ : Test n) (a : ℝ → ℝ)
    (signed : WilsonViewerOriginalProducts.Rows F J Z M simple d v matchMS ν h q g ψ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ y : E → E4, ClearOf 0 y δ → ∀ p : Viewers F,
      let spatial := r^((h:ℝ)+1-1/4)*(∫ x : Points n, ‖ψ x‖)
      ‖RG17.query F (inputs r) y w p r ψ - upon (spectator F p) h 0 y w
        (P r h (prediction R.family d h Z M ν v ψ q (g r)))‖ ≤
        spatial + D*(fee F h*spatial + ‖restore F h‖*(2*a r)) :=
  WilsonViewerOriginalProducts.full F Q J Z M simple run.leading run.obeys d v matchMS ν h q g ψ w
    clearance run.facilities a signed

include run clearance in
theorem Selected.coefficients (K : Set (Points n)) (a : ℝ → Test n → ℝ)
    (signed : ∀ᶠ r in trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
      ∃ᶠ s : ℝ in atTop, ‖(P r h).symm (RG17.basket Q h (inputs r) r ψ) -
        experiment R.family d h Z M ν v ψ ((matchMS.separatedOPE ν).wilson.light h).choose q (g r) s‖ ≤ a r ψ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
      ∀ (o : E4) (y : E → E4), ClearOf o y δ → ∀ p : Viewers F,
      ‖upon (spectator F p) h o y w (RG17.basket Q h (inputs r) r ψ) -
        upon (spectator F p) h o y w (P r h (prediction R.family d h Z M ν v ψ q (g r)))‖ ≤ D*a r ψ :=
  WilsonViewerSignedDictionary.ope F Q J Z M simple run.leading run.obeys matchMS run.facilities.toServices
    ν d h q v w clearance g K a signed

end YM.Integration.WilsonViewerElectedHierarchy
end
