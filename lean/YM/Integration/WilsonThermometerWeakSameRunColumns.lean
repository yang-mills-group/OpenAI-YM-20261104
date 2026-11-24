import YM.Integration.WilsonThermometerOrdinaryPanels
import YM.Integration.WilsonThermometerSmallStationPrice
import YM.Frontier6.Multi.Seams.Shift

/-! Displaced signed measurements of the actual weak-station columns on all
three native reflected panels, retaining the paid fields at their independent sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSameRunColumns
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
open Next.Rank.Price Next.Rank.Tapes.West Next.Rank.Station Next.Rank.East
open Further.CorrectedLift MergeProof MergeProof.East MergeProof.Accent
open PhysicalNext.Repeat.Legato YM.Integration.WilsonLimitConstruction YM.Integration.WilsonPositionThermometerStationNorm
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem original (simple : G.Simple) (panels : R2I.RG05Joint.AcrossPanels R.kit)
    (f : Extraction.Order) (H : (Cells.standard C).Hierarchy) (D : ℕ)
    {I : Type*} [Fintype I] (g : I → Fin (D+1)) (ε : ℝ) (pos : 0<ε) :
    ∃ (P : Fin 3 → Tapes.Panel D) (κ : ℝ),
      Checks (P 0).arc (P 1).arc (P 2).arc κ (trays D) D ∧
      ∀ x : Fin 3, ∃ Q : I→ℝ, (∀ i,0≤Q i) ∧ ∀ᶠ k : ℕ in atTop,
        ∀ᶠ N : ℕ in atTop, ∃ late : k<N, ∀ p (m : ℕ)
        (small : m ≤ widthSky A (P x).arc k) (v : I→Site (R.family.side m p))
        (o : I→Site (R.family.side N p)) {D' : ℕ} (V : Vane C D')
        (j : I→Fin (D'+1)) (w : ∀ i, (Cells.standard C).Field (j i)),
        let hk := (widerSky A (P x).arc k).trans ((beforeSky A (P x).arc k).trans late.le)
        let T := center (R.family.S) p (small.trans hk) 0
        (∀ i,(j i).val=(g i).val) → V.k=k → V.checked f H D' →
        (∀ i,o i ∈ T.margin (v i) (3*span (R.family.S) hk p)) →
          ∀ i, ∃ F, Interior (T.chamber 0) F ∧
            T.rootTest (R.family.beta N p) F ≤ Q i*((A).clock.hatBeta k)^ε*(cost C (g i)*‖w i‖) ∧
            T.copy (v i) F = R.family.O N p (V.wheel.atCut (N,p) (j i) (w i)) (o i) := by
  obtain ⟨K,O,z,_,wage,offered,_⟩ := WilsonThermometerOrdinaryPanels.original R panels
  obtain ⟨P,b,κ,sizes,prices,large⟩ := (offered D).earns
  let A0 := P 0
  have zero : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have same (i : Fin 3) : (A0 i).arc=b i := by simpa [A0] using (prices 0 zero i).1
  have geometry : Checks (A0 0).arc (A0 1).arc (A0 2).arc κ (trays D) D := by
    simpa only [same] using sizes
  refine ⟨A0,κ,geometry,?_⟩
  let panels' : ℕ→Fin 3→Tapes.Panel D := fun _ => A0
  have arcs : ArcSky panels' :=
    ⟨⟨fun x => (A0 x).arc, fun _ => 0,fun _ => ⟨le_rfl,zero_le_one⟩,fun _ _ => (add_zero _).symm⟩,
      fun x => ⟨(A0 x).currency,fun _ => rfl⟩, fun x => ⟨(A0 x).θ,fun _=>rfl⟩⟩
  intro x
  choose Q nonneg paid using fun i:I => small_station (n:=D+2) panels' arcs K R.makes simple
    (R.again simple).1.scrim O (Next.Foundations.chart G) (z D) (fun t ht => wage t D ht)
    f H (by omega) x (g i) ε pos
  refine ⟨Q,nonneg,?_⟩
  filter_upwards [large,eventually_all.mpr paid] with k earned atK
  obtain ⟨Y,seated⟩ := earned 0 zero
  filter_upwards [eventually_all.mpr (fun i:I => atK i Y seated),eventually_ge_atTop (k+1)]
    with N bills later
  have late : k<N := by omega
  refine ⟨late,fun p m small v o D' V j w grades week checked margins => ?_⟩
  have hk := (widerSky A (A0 x).arc k).trans ((beforeSky A (A0 x).arc k).trans late.le)
  let T := center (R.family.S) p (small.trans hk) 0
  let bill i := Q i*((A).clock.hatBeta k)^ε*(cost C (g i)*‖w i‖)
  have fitted (i:I) : ∃ F, Interior (T.chamber 0) F ∧
      T.rootTest (R.family.beta N p) F ≤ bill i ∧
      T.copy (v i) F = R.family.O N p (V.wheel.atCut (N,p) (j i) (w i)) (o i) := by
    obtain ⟨_,_,reported⟩ := bills i p V (j i) (grades i) week checked (w i)
    obtain ⟨F,inside,price,agrees⟩ := Frontier6.Platform.moved_basis R.makes hk small (v i)
      (reported 0).1 (reported 0).2 (margins i)
    refine ⟨F,inside,price,agrees.trans ?_⟩
    funext U
    change R.family.O N p _ 0 (Lattice.translate (o i) U) = _
    rw [R.family.translation,zero_add]
  exact fitted
end YM.Integration.WilsonThermometerWeakSameRunColumns
