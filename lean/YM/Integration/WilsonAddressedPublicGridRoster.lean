import YM.Integration.WilsonAddressedPublicOriginalFaces

/-! One real Wilson census for an arbitrary finite family of published fields,
with its own scalar restoration at each occupied root. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedPublicGridRoster
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    {l : Ultrafilter (ℕ×ℕ)} {D : ℕ} {g : ℝ → ℝ} {U : ℝ}
local notation "C₀" => R.family

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (A : Pool R (l:=l) F D g U) :
    ∃ t ≥ D+3, ∀ᶠ r in trail, ∀ p N (deep : A.j r < N),
    ∃ (V : (a : Fin (D+1)) → Sight C₀ a.val p) (u : (a : Fin (D+1)) → Emblems C₀ a.val)
      (est : ∀ a : Fin (D+1), Opened C₀ a.val (A.j r) p),
    (∀ a, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) (A.j r) N p a.val
      (digits R N p 0) (V a) (u a)) ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (d : I → Fin (D+1)) (v : (i : I) → S.Field (d i).val)
      (c : I → Site ((C₀).side (A.j r) p)) (names : Census I),
    (∀ i j : I, i≠j → ((C₀).path.levels.budget (A.j r)).B^2 <
      separation (point R (N:=N) 0 (1,false) (c i) (A.j r)) (point R (N:=N) 0 (1,false) (c j) (A.j r))) →
    let x := fun i => A.field (d i) r (v i) (N,p)
    let y := fun i => offer R (x i) (est (d i)) deep.le
    let b := fun i => anchorAt R (c i) N
    let data := fun i => reduce (y i)
    (∀ i, charge (y i) ≤ max 1 (2*(A.B r*GapsContact.Ascent.cost F (d i).val (A.ρ r) (v i)))) ∧
    WilsonThermometerReflectedRoster.filed R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
      data (fun i => V (d i)) (fun i => u (d i)) names deep.le t ∧
    ∀ j (hj : j ≤ N) (s : names.Mode) T,
      (WilsonThermometerReflectedRoster.density R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
        data (fun i => u (d i)) names deep.le hj T).part s =
      ((C₀).path.rep N p j).eval T • actualTransport C₀ (N:=N)
        (fun W => ∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) hj T := by
  classical
  obtain ⟨t,tp,roster⟩ := WilsonThermometerReflectedRoster.original R simple shop D
  have awake : ∀ᶠ k:ℕ in atTop, ∀ a : Fin (D+1),
      Awake (C:=C₀) R.doors (WilsonThermometerOffsetLedger.cash R) k a.val :=
    Filter.eventually_all.mpr fun a => (WilsonThermometerOffsetLedger.original R simple shop a.val).mono fun _ h => h.1
  have opening : ∀ᶠ k:ℕ in atTop, ∀ a : Fin (D+1), ∀p, Opened C₀ a.val k p :=
    Filter.eventually_all.mpr fun a => open_late C₀ simple a.val
  refine ⟨t,tp,?_⟩
  filter_upwards [A.enters.eventually roster,A.enters.eventually awake,A.enters.eventually opening,A.standing]
    with r placed wages joints press p N deep
  choose V u enrolled using fun a : Fin (D+1) => enroll R.makes (wages a) deep.le (digits R N p 0)
  refine ⟨V,u,fun a => joints a p,enrolled,?_⟩
  intro I fi di d v c names room x y b data
  have refs (i : I) (e : ℕ) (he : e ≤ (d i).val) : (C₀).ref e ≤ N :=
    (joints ⟨e,Nat.lt_of_le_of_lt he (d i).isLt⟩ p).post.trans deep.le
  have state := placed p N deep.le I (fun i => (d i).val) (fun i => Nat.le_of_lt_succ (d i).isLt)
    (fun _ => 0) (fun i => V (d i)) (fun i => u (d i)) (fun i => enrolled (d i))
    (fun _ => (1,false)) c room names data (fun i => WilsonThermometerMarchSource.small (y i))
  refine ⟨fun i => salary R F _ _ _ _ (joints (d i) p) deep.le _ _ (enrolled (d i)) (refs i)
    (((press (d i)).2 (v i)).1 N p deep),state,?_⟩
  exact WilsonAddressedPublicOriginalFaces.original R (fun i => (d i).val) x (fun i => V (d i)) (fun i => u (d i))
    (fun i => joints (d i) p) deep.le (fun i => enrolled (d i)) refs c names t state

end YM.Integration.WilsonAddressedPublicGridRoster
end
