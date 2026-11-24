import YM.MS.Graphical.CommonGates
import YM.FVA2.Teller.Mass
import YM.MS.ScaleForest.Calibrate
import YM.MS.ScaleForest.Halves
import YM.MS.ScaleForest.Warming

noncomputable section
namespace YM.MS.ScaleForest.Panels
open Function Filter Set MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Local.Physical
open Planted FVA2 FVA2.Position FVA2.Position.Axes FVA2.Arrival Dframe WilsonMS
open Normalize.Fray
open scoped Topology Classical BigOperators ENNReal
variable {G : Gauge} {n d : ℕ}
local notation "O" => OpenAxis.Plot (Press.portDeck G)


noncomputable def _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.physicalScale : ℝ :=
  YM.FVA2.Teller.logNu 1

open YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest (physicalScale)

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.calibration : physicalScale = (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 :=
  YM.FVA2.Teller.calibration

noncomputable def _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.film (K : Set (Points n)) (v : Tags G d n) (k : ℕ)
    (s : ℝ) (z : ℂ) (x : ↥K) : ℂ :=
  ∑ Y : Fin n → Toon G d, capsule (bicolor G) physicalScale K Y k s z x * each Y v

noncomputable def _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.released (K : Set (Points n)) (v : Tags G d n) (k : ℕ)
    (s : ℝ) (x : ↥K) : ℂ :=
  ∑ Y : Fin n → Toon G d, at_time (bicolor G) physicalScale K Y k s x * each Y v

open YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest (film released)

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.expanded (K : Set (Points n)) (v : Tags G d n) (k : ℕ)
    (s : ℝ) (z : ℂ) (x : ↥K) :
    film K v k s z x =
      ∑ Y : Fin n → Toon G d, byPartition (fun S j =>
        fundraiser physicalScale (atlas (bicolor G) (inducted O ∘ flash ∘ Y)
          (onM K) S j).2 z s x 0 []) Finset.univ k * each Y v ∧
    released K v k s x =
      ∑ Y : Fin n → Toon G d, byPartition (fun S j =>
        costTable physicalScale (atlas (bicolor G) (inducted O ∘ flash ∘ Y)
          (onM K) S j).2 x s 0 []) Finset.univ k * each Y v := ⟨rfl, rfl⟩

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.vacuum (K : Set (Points n)) (Y : Fin n → Toon G d)
    (k : ℕ) (s : ℝ) (z : ℂ) (x : ↥K) :
    byPartition (staying (bicolor G) (inducted O ∘ flash ∘ Y)
      physicalScale (onM K) s z x) ∅ k = (if k = 0 then 1 else 0) ∧
    byPartition (stayed (bicolor G) (inducted O ∘ flash ∘ Y)
      physicalScale (onM K) s x) ∅ k = (if k = 0 then 1 else 0) := by
  have unit (f : Finset (Fin n) → T ℂ) :
      byPartition f ∅ k = (if k = 0 then 1 else 0) := by simp [byPartition, joinsP]
  exact ⟨unit _, unit _⟩

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.sameBook (M : YM.MS.Land.MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (x : Points n) (hx : x ∈ conf n) (k : ℕ) :
    YM.MS.Graphical.separatedGraphSum physicalScale G d x k = Dframe.meteor physicalScale M d x k :=
  YM.MS.Graphical.identification_screen physicalScale M hx

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.row (x : Points n) (hx : x ∈ conf n) (k : ℕ) :
    stage (bicolor G) physicalScale d x k = YM.MS.Graphical.separatedGraphSum physicalScale G d x k :=
  (tracked (bicolor G) physicalScale (stock G) x hx k).trans
    (YM.MS.Graphical.identification_screen physicalScale (stock G) hx).symm

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.basis (x : Points n) (hx : x ∈ conf n) (v : Tags G d n) (k : ℕ) :
    YM.MS.Graphical.separatedGraphSum physicalScale G d x k v =
      ∑ Y : Fin n → Toon G d, gross (bicolor G) physicalScale Y k x * each Y v := by
  rw [← YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.row x hx k]
  simp only [stage, sum_apply, smul_apply]
  rfl

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.compact (K : Set (Points n)) (hk : IsCompact K)
    (hp : K ⊆ conf n) (v : Tags G d n) (k : ℕ) :
    (∀ s, Stills dotty (film K v k s) (released K v k s)) ∧
    Stills atTop (released K v k)
      (fun x : ↥K => YM.MS.Graphical.separatedGraphSum physicalScale G d x.val k v) := by
  haveI := isCompact_iff_compactSpace.mp hk
  constructor
  · intro s
    unfold YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.film YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.released
    exact Stills.taleSum _
      (F := fun Y z x => capsule (bicolor G) physicalScale K Y k s z x * each Y v)
      (fun Y _ => Stills.mul ((still_gross (bicolor G) physicalScale k K Y hk hp).1 s)
        (Stills.strokes continuous_const))
  · have value : (fun x : ↥K => YM.MS.Graphical.separatedGraphSum physicalScale G d x.val k v) =
        (fun x : ↥K => ∑ Y : Fin n → Toon G d,
          gross (bicolor G) physicalScale Y k x.val * each Y v) :=
      funext fun x => YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.basis x.val (hp x.property) v k
    rw [value]
    unfold released
    exact Stills.taleSum _
      (F := fun Y s x => at_time (bicolor G) physicalScale K Y k s x * each Y v)
      (fun Y _ => Stills.mul ((still_gross (bicolor G) physicalScale k K Y hk hp).2)
        (Stills.strokes continuous_const))

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.physical (x : Points n) (hx : x ∈ conf n) (v : Tags G d n) (k : ℕ) :
    let K : Set (Points n) := {x}
    let u : ↥K := ⟨x, Set.mem_singleton x⟩
    (∀ ρ : ℝ, 0 < ρ → Tendsto (fun z => film K v k (Real.log ρ) z u) dotty
      (𝓝 (released K v k (Real.log ρ) u))) ∧
    Tendsto (fun ρ : ℝ => released K v k (Real.log ρ) u) atTop
      (𝓝 (YM.MS.Graphical.separatedGraphSum physicalScale G d x k v)) := by
  intro K u
  obtain ⟨hz, hi⟩ := YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.compact K isCompact_singleton (Set.singleton_subset_iff.mpr hx) v k
  exact ⟨fun ρ _ => (hz (Real.log ρ)).stillPoint u, (hi.stillPoint u).comp Real.tendsto_log_atTop⟩

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.tested (p : Test n) (v : Tags G d n) (k : ℕ) :
    let K := tsupport p
    (∀ s, Tendsto (fun z => averaging p (film K v k s z)) dotty
      (𝓝 (averaging p (released K v k s)))) ∧
    Tendsto (fun s => averaging p (released K v k s)) atTop
      (𝓝 (averaging p (fun x : ↥K => YM.MS.Graphical.separatedGraphSum physicalScale G d x.val k v))) := by
  intro K
  obtain ⟨hz, hi⟩ := YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.compact K p.hasCompactSupport p.tsupport_subset v k
  exact ⟨fun s => (still_covers p (hz s)).2, (still_covers p hi).2⟩

theorem _root_.YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.original (M : YM.MS.Land.MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (K : Set (Points n)) (hk : IsCompact K) (hp : K ⊆ conf n) (v : Tags G d n) (k : ℕ) :
    (∀ s, Stills dotty (film K v k s) (released K v k s)) ∧
    Stills atTop (released K v k)
      (fun x : ↥K => YM.MS.Graphical.separatedGraphSum physicalScale G d x.val k v) ∧
    ∀ x : ↥K, YM.MS.Graphical.separatedGraphSum physicalScale G d x.val k =
      Dframe.meteor physicalScale M d x.val k := by
  obtain ⟨dimensional, infrared⟩ := YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.compact K hk hp v k
  exact ⟨dimensional, infrared, fun x => YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.sameBook M x.val (hp x.property) k⟩

end YM.MS.ScaleForest.Panels
