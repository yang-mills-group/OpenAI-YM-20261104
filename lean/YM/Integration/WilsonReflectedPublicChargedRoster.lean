import YM.Integration.WilsonReflectedPublicOrientedFaces
import YM.Integration.WilsonInvariantActionCaptureCharge
/-! The actual reduced single-site declarations, served together at a chosen
common reporter, before choosing original cutoff lifts, signed orientations
and spatial test vectors. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicChargedRoster
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) :
    ∃ t ≥ D+3, ∀ᶠ k:ℕ in atTop, ∀ p N (deep:k<N),
    ∃ (V:(a:Fin (D+1)) → Sight C₀ a.val p) (u:(a:Fin (D+1)) → Emblems C₀ a.val)
      (est:∀a:Fin (D+1), Opened C₀ a.val k p),
    (∀a, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p a.val
      (digits R N p 0) (V a) (u a)) ∧
    ∀ (I:Type) [Fintype I] [DecidableEq I] (d:I → Fin (D+1)) (x:(i:I) → (C₀).label (d i).val)
      (turn:I → Motion) (c:I → Site ((C₀).side k p)) (names:Census I),
    (∀ i j:I, i≠j → ((C₀).path.levels.budget k).B^2 <
      separation (point R (N:=N) 0 (turn i) (c i) k) (point R (N:=N) 0 (turn j) (c j) k)) →
    let y := fun i => offer R (x i) (est (d i)) deep.le
    let b := fun i => anchorAt R (c i) N
    let data := fun i => reduce (y i)
    (∀i, charge (y i) ≤ max 1 (2*((C₀).S.a k^(d i).val)⁻¹*Next.UVStress.quota C₀ (d i).val k N p (x i))) ∧
    WilsonThermometerReflectedRoster.filed R (fun i => (d i).val) (fun _ => 0) turn c data
      (fun i => V (d i)) (fun i => u (d i)) names deep.le t ∧
    ∀ j (hj:j≤N) (s:names.Mode) U,
      (WilsonThermometerReflectedRoster.density R (fun i => (d i).val) (fun _ => 0) turn c data
        (fun i => u (d i)) names deep.le hj U).part s =
      ((C₀).path.rep N p j).eval U • actualTransport C₀ (N:=N)
        (fun W => ∏i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p
          (displayed R (d i).val (x i) (turn i)) (b i) W) hj U := by
  classical
  obtain ⟨t,tp,roster⟩ := WilsonThermometerReflectedRoster.original R simple shop D
  have awake : ∀ᶠ k:ℕ in atTop, ∀ a : Fin (D+1),
      Awake (C:=C₀) R.doors (WilsonThermometerOffsetLedger.cash R) k a.val :=
    Filter.eventually_all.mpr fun a => (WilsonThermometerOffsetLedger.original R simple shop a.val).mono fun _ h => h.1
  have opening : ∀ᶠ k:ℕ in atTop, ∀ a : Fin (D+1), ∀p, Opened C₀ a.val k p :=
    Filter.eventually_all.mpr fun a => open_late C₀ simple a.val
  refine ⟨t,tp,?_⟩
  filter_upwards [roster,awake,opening] with k placed wages joints p N deep
  choose V u enrolled using fun a : Fin (D+1) => enroll R.makes (wages a) deep.le (digits R N p 0)
  refine ⟨V,u,fun a => joints a p,enrolled,?_⟩
  intro I fi di d x turn c names room y b data
  have refs (i:I) (e:ℕ) (he:e≤(d i).val) : (C₀).ref e≤N :=
    (joints ⟨e,Nat.lt_of_le_of_lt he (d i).isLt⟩ p).post.trans deep.le
  have filed := placed p N deep.le I (fun i => (d i).val) (fun i => Nat.le_of_lt_succ (d i).isLt)
    (fun _ => 0) (fun i => V (d i)) (fun i => u (d i)) (fun i => enrolled (d i))
    turn c room names data (fun i => small (y i))
  refine ⟨?_,filed,WilsonReflectedPublicOrientedFaces.original R (fun i => (d i).val) x
    (fun i => V (d i)) (fun i => u (d i)) (fun i => joints (d i) p) deep.le
    (fun i => enrolled (d i)) refs turn c names t filed⟩
  intro i
  have paid := (WilsonAddressedAlignedColumn.original R (enrolled (d i)) deep.le le_rfl
    (refs i) (joints (d i) p) (x i)).2
  change size (y i) ≤ 2*Spindle.paid C₀ (d i).val k N p (x i) at paid
  rw [WilsonInvariantActionCaptureCharge.amount,←mul_assoc] at paid
  exact max_le_max_left _ paid

end YM.Integration.WilsonReflectedPublicChargedRoster
end
