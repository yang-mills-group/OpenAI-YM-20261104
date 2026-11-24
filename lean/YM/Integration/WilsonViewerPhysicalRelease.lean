import YM.Integration.WilsonViewerBookedHierarchy

/-! On the booked original physical hierarchy, the signed finite Rose experiment
sets the scale of the moving exterior read. The same complete independent MS
coefficient then tests the ordinary product in every fixed-clearance viewer. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater RG12 SharpGram WilsonPositionSeparatedProfileMatching
open WilsonMSDictionaryVector WilsonPositionHomogeneousFrame WilsonPositionThermometerCapStation
open WilsonPositionCapTransport WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonMacroscopicRichTwoDatePivot WilsonPublicOutputSmooth
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin} {J : ℝ → PhysMS.tower S}
    {Y : (Bel R.family.book).Hierarchy} {arch : Trace.Terrace.Arch R.family}
    {ℓ : Ultrafilter (ℕ × ℕ)} {cohort : Ultrafilter (ℕ × ℕ) → Prop} {simple : G.Simple}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {branch : Bool} (ms : Main.Match Z simple M σ branch)
    (rose : ℝ → Group R.family 6) (book : Book (f:=f) (l:=ℓ) (H:=Y) rose J)
    {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit) (fine index : ℝ → ℕ)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index
local notation "issued" => WilsonMaxwellThermometerKineticRequest.earned (Y:=ℓ) Z F J rose simple (B:=B) fine index

/-- Numerical hypotheses on the positioned genuine original product and the
preselected independently regulated product at the very same exterior rows. -/
def purchasedRows (ν : ℝ) {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    (h q P E A : ℕ) (panel : Profiles R h) (probe : panel.probes.index → Atom (R:=R) h)
    (site : ∀ j, panel.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (probe j))
    (K : Set (Points n)) (C D : Test n → ℝ) : Prop :=
  ∀ᶠ r in trail, let t := r/((θ r)^A)^2
    ∀ tp : 0<t, ∀ ψ : Test n, tsupport ψ ⊆ K →
      let a := fun i => pub r (d i) (v i)
      let X := exterior F J Z panel probe site tp
      let actual := RG17.basket Q h a r ψ
      let read := fun j => RG17.appeared F a (X j) r ψ
      let value := fun s => experiment R.family d h Z M ν v ψ ((ms.separatedOPE ν).wilson.light h).choose q (θ r) s
      ‖(fun j => (X j).charge F h actual) - read‖ ≤ C ψ * (((θ r)^A)^2)^(h+1)/(θ r)^E ∧
      ∃ᶠ s : ℝ in atTop, ‖read-(fun j => (X j).charge F h (pub r h (value s)))‖ ≤ D ψ*(θ r)^(P+A*(2*h+1))

include run book hB pace in
theorem Selected.public (schedule : enrolled) (ν : ℝ) {m : ℕ} (d₀ : ℕ) (φ : Test m)
    (v₀ : Fin m → Sec G d₀) (q₀ : ℕ) (first : issued d₀ φ v₀ 1) (target : 0 < q₀ → issued d₀ φ v₀ q₀)
    (h : ℕ) :
    Coupling G θ ∧ matchesThrough Z M F J ν d₀ φ v₀ q₀ ∧ LogTrace F Q.port ∧
    ∃ panel : Profiles R h, ∃ probe : panel.probes.index → Atom (R:=R) h,
    ∃ site : ∀ j, panel.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (probe j),
    ∀ P E A : ℕ, P+E ≤ A → ∀ {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
      (q : ℕ) (K : Set (Points n)), IsCompact K → K ⊆ conf n → ∀ C D : Test n → ℝ,
      (∀ ψ, 0≤C ψ) → purchasedRows Z M ms (F:=F) (Q:=Q) (J:=J) ν d v h q P E A panel probe site K C D →
      ∀ {I : Type} [Fintype I] {e : I → ℕ} (w : Labels S e) {δ η : ℝ}, 0<δ → 0<η →
      ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ r in trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
        ∀ y : I → E4, ClearOf 0 y δ → ∀ p : Viewers F,
        ‖RG17.query F (fun i => pub r (d i) (v i)) y w p r ψ -
          upon (spectator F p) h 0 y w (pub r h (prediction R.family d h Z M ν v ψ q (θ r)))‖ ≤
          r^((h:ℝ)+1-η) * (∫ x : Points n, ‖ψ x‖) + V * (C ψ + D ψ) * (θ r)^P := by
  obtain ⟨_,_,X,_,_,_⟩ := run.bliss.picks (fun i : ℕ => 1/((i:ℝ)+1))
    tendsto_one_div_add_atTop_nhds_zero_nat (fun i => by positivity)
  obtain ⟨genuine,correlation⟩ := WilsonMaxwellThermometerKineticRelease.original Z F J rose simple hB pace
    fine index run.bliss book run.leading ms schedule ν Q run.obeys X run.foundation d₀ φ v₀ q₀ first target
  obtain ⟨sharp,panel,probe,site,cost,ok,decode⟩ := WilsonPublicOutputSmooth.original F J Z M ν ms
    run.leading run.obeys Q run.facilities run.original run.matrix h
  refine ⟨genuine,correlation,sharp,panel,probe,site,?_⟩
  intro P E A enough n d v q K compact separated C D nonneg sales I fI e w δ η clear slack
  have detector : ∀ᶠ r in trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
      ∃ᶠ s : ℝ in atTop, ‖(pub r h).symm (RG17.basket Q h (fun i => pub r (d i) (v i)) r ψ) -
        experiment R.family d h Z M ν v ψ ((ms.separatedOPE ν).wilson.light h).choose q (θ r) s‖ ≤
        cost * (C ψ + D ψ) * (θ r)^P := by
    filter_upwards [decode θ genuine P E A enough,sales] with r face invoice ψ hs
    obtain ⟨tp,atNode⟩ := face
    obtain ⟨spatial,signed⟩ := invoice tp ψ hs
    exact (atNode n d v ψ q (C ψ) (D ψ) (nonneg ψ) spatial signed).1
  let price := fun r ψ => cost * (C ψ + D ψ) * (θ r)^P
  have clock : ∃ T : ℝ, 0<T ∧ ∀ᶠ r in trail, θ r ≤ T*|θ r| :=
    ⟨1,zero_lt_one,Eventually.of_forall fun r => (le_abs_self _).trans_eq (one_mul _).symm⟩
  obtain ⟨V,Vn,bound⟩ := (run.joined Z M ms ν d₀ φ v₀ q₀ θ genuine clock
    (fun ε ep => (correlation ε ep).mono fun _ k => k none) d v h q compact separated w
    clear slack price detector).2
  refine ⟨V*cost,mul_nonneg Vn ok,?_⟩
  filter_upwards [bound] with r room ψ hs y distance p
  exact (room ψ hs y distance p).trans_eq (by dsimp [price]; ring)

end YM.Integration.WilsonViewerElectedHierarchy
end
