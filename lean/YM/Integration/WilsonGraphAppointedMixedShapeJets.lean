import YM.Integration.WilsonGraphAppointedStationaryPrices
import YM.GradedFar.Lay

noncomputable section
namespace YM.Integration.WilsonGraphAppointedMixedShapeJets

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level FVA2.GradedFar
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Neighbor Integration.GradedFar.Tariff
open Integration.GradedFar.Tariff.Sunshine
open scoped Topology BigOperators Classical ContDiff

section Fields
variable {G : Gauge} {C : Family G} {S : Table C.book} {e : Extraction.Order}
variable (F : Final C e S) (P : ℝ → tower S)

/-- At each finite upper grade, the actually paid adjacent maps compose on the elected field. -/
theorem included (adjacent : ∀ i, Included F P i (i+1) (Nat.le_succ i))
    {d h : ℕ} (hd : d ≤ h) : Included F P d h hd := by
  induction hd with
  | refl =>
    apply Filter.Eventually.of_forall
    intro r u
    have same : Normalize.up (Nat.le_refl d) u = u := Subtype.ext rfl
    rw [same, F.sector.derivatives.arrival (spectate F none).laws.toSymmetric (spectate_ready F none)]
  | @step h hd ih =>
    filter_upwards [ih, adjacent h] with r previous next
    intro u
    have joined : Normalize.up (Nat.le_succ h) (Normalize.up hd u) =
        Normalize.up (Nat.le.step hd) u := Subtype.ext rfl
    rw [← joined, next (Normalize.up hd u), previous u]
    exact F.sector.derivatives.transit (spectate F none).laws.toSymmetric
      (spectate_ready F none) hd (Nat.le_succ h) _

/-- Translation covariance and the original inclusion theorem act on the same compact
shape. The equality holds on the full separated chart for every physical center. -/
theorem centers (adjacent : ∀ i, Included F P i (i+1) (Nat.le_succ i))
    {n h : ℕ} {d : Fin n → ℕ} (within : Through h d) :
    ∀ᶠ r in trail, ∀ (viewer : Viewers F) (o : E4) (u : Inputs G d),
      EqOn (fun y => TrueCompact F P viewer r o y u)
        (fun y => frank F P viewer h r y (FVA2.GradedFar.raised within u)) (conf n) := by
  have rows : ∀ᶠ r in trail, ∀ i : Fin n, ∀ u : Sec G (d i),
      assign P r h (Normalize.up (within i) u) =
        F.sector.derivatives.rise (within i) (assign P r (d i) u) :=
    Filter.eventually_all.mpr fun i => included F P adjacent (within i)
  filter_upwards [rows, show ∀ᶠ r in trail, 0 < r from self_mem_nhdsWithin] with r hw hr
  intro viewer o u x hx
  exact (atTable_within F P viewer d u o hr hx).symm.trans
    (frank_inclusion F P within hr viewer hw u hx).symm
end Fields

universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable (Z : WilsonPrescription G) (V : Vision E ξ) (Q : Perspective H Z true)
local notation "t" => V.T Z
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion
local notation "field" => V.pupil.last
local notation "W" => V.Post Z

include V Q in
theorem cropSmooth {n : ℕ} (h p : ℕ) (s : ℝ) (v : Fin n → Sec G h) :
    ContDiffOn ℝ ∞ (fun x : Points n => FVA2.GradedFar.crop p s (sent X h x v)) (conf n) := by
  simp_rw [FVA2.GradedFar.crop_eq]
  apply ContDiffOn.sum
  intro i hi
  apply contDiffOn_const.mul
  exact WilsonGraphCompactCoordinateJets.smoothCoefficients field W Z Q.MS Q.matching
    (marks_the_data Z V Q).clock (WilsonGraphAppointedStationaryPrices.adjacent Z V Q)
    (WilsonGraphAppointedStationaryPrices.stationary Z V Q 2)
    (WilsonGraphAppointedStationaryPrices.stationary Z V Q n) h v i

include Q in
theorem coordinate {ι : Type} {I : Type*} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n h : ℕ} {d : Fin n → ℕ} (within : Through h d) (u : Inputs G d)
    (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n)
    (active : ι → I → Prop) (point : ι → I → Points n)
    (placed : ∀ s i, active s i → point s i ∈ K) (viewer : ι → I → Peers V)
    (origin : ι → I → E4) (p : ℕ) (word : TraceOrder n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ i, active s i →
      ‖δ word (fun y => TrueCompact field W (viewer s i) (r s) (origin s i) y u) (point s i) -
        δ word (fun y => FVA2.GradedFar.crop p (t (r s)) (sent X h y (FVA2.GradedFar.raised within u))) (point s i)‖ ≤
          A * |t (r s)|^(p+1) := by
  have scalar (cap : ℕ) (v : Fin n → Sec G cap) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in l, ∀ i, active s i →
        ‖frank field W (viewer s i) cap (r s) (point s i) v -
          FVA2.GradedFar.crop p (t (r s)) (sent X cap (point s i) v)‖ ≤ C * |t (r s)|^(p+1) := by
    obtain ⟨C,hC,price⟩ := WilsonGraphAppointedStationaryPrices.value Z V Q l r scale K hK separated
      (FVA2.Teller.logNu 1) cap p v
    exact ⟨C,hC,price.mono fun s hs i hi => hs (viewer s i) (point s i) (placed s i hi)⟩
  have connected := WilsonGraphAppointedStationaryPrices.adjacent Z V Q
  obtain ⟨A,hA,price⟩ := WilsonGraphCompactCoordinateJets.compact field W Z Q.MS Q.matching
    l r scale point viewer (marks_the_data Z V Q).clock connected hK separated placed
    (WilsonGraphAppointedStationaryPrices.stationary Z V Q 2)
    (WilsonGraphAppointedStationaryPrices.stationary Z V Q n) scalar h word (FVA2.GradedFar.raised within u)
  refine ⟨A,hA,?_⟩
  filter_upwards [price, scale.eventually (centers field W connected within)] with s hs he
  intro i hi
  rw [δ_congr (conf_open n) (he (viewer s i) (origin s i) u) word (separated (placed s i hi))]
  exact hs i hi

include Q in
/-- The full Fréchet jet of the mixed-grade Wilson moment, at every filed center and
viewer, has the same compact asymptotic price as its finite, normalized position series. -/
theorem original {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n h : ℕ} {d : Fin n → ℕ} (within : Through h d) (u : Inputs G d)
    (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n) (p j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
      YangMills.Matching.shapeJetEstimateAt j
        (fun y => TrueCompact field W viewer (r s) o y u)
        (fun y => FVA2.GradedFar.crop p (t (r s)) (sent X h y (FVA2.GradedFar.raised within u)))
        x (A * |t (r s)|^(p+1)) := by
  let I := Peers V × E4 × K
  let current (s : ι) (i : I) (y : Points n) := TrueCompact field W i.1 (r s) i.2.1 y u
  let formal (s : ι) (_ : I) (y : Points n) :=
    FVA2.GradedFar.crop p (t (r s)) (sent X h y (FVA2.GradedFar.raised within u))
  let point (_ : ι) (i : I) : Points n := i.2.2.val
  let err (s : ι) (_ : I) := |t (r s)|^(p+1)
  have connected := WilsonGraphAppointedStationaryPrices.adjacent Z V Q
  have paid := WilsonGraphCompactCoordinateJets.original (I := fun _ => I)
    l j current formal point err (fun s _ => pow_nonneg (abs_nonneg _) _) 
  have smooth : ∀ᶠ s in l, ∀ i : I, point s i ∈ conf n ∧
      ContDiffOn ℝ ∞ (current s i) (conf n) ∧ ContDiffOn ℝ ∞ (formal s i) (conf n) := by
    filter_upwards [scale.eventually (centers field W connected within),
      scale.eventually (show ∀ᶠ z in trail, 0 < z from self_mem_nhdsWithin)] with s he hr
    intro i
    refine ⟨separated i.2.2.property, ?_, cropSmooth Z V Q h p _ _⟩
    exact (true_views field W i.1 hr (FVA2.GradedFar.raised within u)).congr (he i.1 i.2.1 u)
  obtain ⟨A,hA,hp⟩ := paid smooth (fun word => by
    obtain ⟨C,hC,priced⟩ := coordinate Z V Q l r scale within u K hK separated
      (fun (_ : ι) (_ : I) => True) point (fun _ i _ => i.2.2.property)
      (fun _ i => i.1) (fun _ i => i.2.1) p word
    exact ⟨C,hC,priced.mono fun s hs i => hs i trivial⟩)
  refine ⟨A,hA,?_⟩
  filter_upwards [hp] with s hs
  intro viewer o x hx
  exact hs (viewer,o,⟨x,hx⟩)

end YM.Integration.WilsonGraphAppointedMixedShapeJets
