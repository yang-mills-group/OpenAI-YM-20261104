import YM.Integration.WilsonSharpPhysicalTreeDetectorSweep
import YM.Integration.WilsonMacroscopicViewerCharge

/-! Sharp physical spectator remainder on an arbitrary original tree. The same
exterior is used in the whole correlation and every retained coefficient column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorSpectators
open Function Filter Set MeasureTheory Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Log
open OPE.Prescription OPE.Arboreal OPE.Arboreal.Mountain
open WilsonSharpPhysicalTreeDetectorKernel WilsonSharpPhysicalTreeDetectorResponse
open scoped Classical Topology BigOperators
attribute [local instance] YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I J : Type} [Fintype I] [Fintype J] {g : J→ℕ}

/-- The fixed full reader norm transfers the raw sharp price to the actual retained field. -/
theorem field (trace : LogTrace F Q.port) (s : Arboreal I) (p : I→C.book.Token) (h : ℕ)
    {d : (↑s.leaves : Type)→ℕ} (v : Labels S d) (hp : crop p s.leaves = names v)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ j : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ), t s.root = r → s.Convoy M η t x →
      ∀ k, j ≤ k → ‖Q.packet h (crop x s.leaves) v (x s.root) - shadowOld Q.port h (crop x s.leaves) (x s.root) v‖ ≤
        ‖reader F Q h‖ * s.listPrice p t (h+1) k := by
  obtain ⟨j,rows⟩ := WilsonSharpPhysicalTreeDetectorSweep.original F Q trace s p h v hp hM hη
  refine ⟨j,?_⟩
  filter_upwards [rows] with r atR x t rt fit k jk
  obtain ⟨ok,price⟩ := atR x t rt fit k jk
  rw [error F Q h (crop x s.leaves) v (x s.root) _ ok]
  exact ((reader F Q h).le_opNorm _).trans (mul_le_mul_of_nonneg_left price (norm_nonneg _))

theorem with_geometry (paid : Services C f S) (trace : LogTrace F Q.port) (s : Arboreal I)
    (p : I→C.book.Token) (h : ℕ) {d : (↑s.leaves : Type)→ℕ} (v : Labels S d) (w : Labels S g)
    (hp : crop p s.leaves = names v) {M η c : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) :
    ∃ (k : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ) (y : J→E4),
      t s.root = r → s.Convoy M η t x → ClearOf (x s.root) y c →
      Injective (beside (crop x s.leaves) y) ∧ Injective (beside (sole (x s.root)) y) ∧
      ‖algebraError F Q (crop x s.leaves) (x s.root) v y w h‖ ≤ A * s.listPrice p t (h+1) k ∧
      ∀ q : Viewers F, ‖formula F Q (crop x s.leaves) (x s.root) v y w h q‖ ≤ A * s.listPrice p t (h+1) k := by
  obtain ⟨D,hD,charge⟩ := WilsonMacroscopicViewerCharge.uniform F paid h w hc
  obtain ⟨bs,priced⟩ := trace.testing s p (names w) h M η c hM hη hc
  obtain ⟨bd,detectors⟩ := WilsonSharpPhysicalTreeDetectorSweep.original F Q trace s p h v hp hM hη
  let k := max bs bd
  let A := 1 + D * ‖reader F Q h‖
  have An : 0 ≤ A := add_nonneg zero_le_one (mul_nonneg hD (reader F Q h).opNorm_nonneg)
  refine ⟨k,A,An,?_⟩
  filter_upwards [priced,detectors] with r raw orbit x t y rt fit clear
  let xs := crop x s.leaves
  let o := x s.root
  let b := shadowOld Q.port h xs o v
  let P := Q.packet h xs v o
  let E := s.listPrice p t (h+1) k
  have bill := raw x t y rt fit clear k (le_max_left _ _)
  have ep : 0 ≤ E := (norm_nonneg _).trans bill.ready.compressed
  obtain ⟨valid,fees⟩ := orbit x t rt fit k (le_max_right _ _)
  have packetNorm : ‖P - b‖ ≤ ‖reader F Q h‖ * E := by
    rw [show P-b = reader F Q h (response F Q h xs v o-insertion F Q h o b) from error F Q h xs v o b valid]
    exact ((reader F Q h).le_opNorm _).trans (mul_le_mul_of_nonneg_left fees (norm_nonneg _))
  have all (q : Viewers F) : ‖formula F Q xs o v y w h q‖ ≤ A * E := by
    let T := upon (spectator F q) h o y w
    let wholeQ := whole (spectator F q) xs v y w
    have rb : ‖wholeQ-T b‖ ≤ E := WilsonSharpPhysicalTreeDetectorSweep.raw F Q s p v hp w h bill q
    have cb : ‖T b-T P‖ ≤ D * (‖reader F Q h‖ * E) := by
      rw [← map_sub]
      apply (charge o y clear bill.apertures q (b-P)).trans
      apply mul_le_mul_of_nonneg_left _ hD
      simpa only [norm_sub_rev] using packetNorm
    rw [formula,← packet_read F Q xs o v y w q h bill.apertures]
    change ‖wholeQ - T P‖ ≤ A * E
    calc
      _ ≤ ‖wholeQ - T b‖ + ‖T b - T P‖ := by simpa only [dist_eq_norm] using dist_triangle wholeQ (T b) (T P)
      _ ≤ E + D * (‖reader F Q h‖ * E) := add_le_add rb cb
      _ = A * E := by unfold A; ring
  refine ⟨bill.right,bill.apertures,?_,all⟩
  apply (glance_contract F (mul_nonneg An ep)).2
  intro q
  rw [formula_seen F Q _ _ _ _ _ _ _ bill.right bill.apertures]
  exact all q

theorem original (paid : Services C f S) (trace : LogTrace F Q.port) (s : Arboreal I)
    (p : I→C.book.Token) (h : ℕ) {d : (↑s.leaves : Type)→ℕ} (v : Labels S d) (w : Labels S g)
    (hp : crop p s.leaves = names v) {M η c : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) :
    ∃ (k : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ) (y : J→E4),
      t s.root = r → s.Convoy M η t x → ClearOf (x s.root) y c →
      ‖algebraError F Q (crop x s.leaves) (x s.root) v y w h‖ ≤ A * s.listPrice p t (h+1) k ∧
      ∀ q : Viewers F, ‖formula F Q (crop x s.leaves) (x s.root) v y w h q‖ ≤ A * s.listPrice p t (h+1) k := by
  obtain ⟨k,A,hA,rows⟩ := with_geometry F Q paid trace s p h v w hp hM hη hc
  refine ⟨k,A,hA,?_⟩
  filter_upwards [rows] with r atR x t y rt fit clear
  exact (atR x t y rt fit clear).2.2

/-- The same already-elected matrix ticket supplies the raw sharp testing input. -/
theorem on_ticket (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (hu : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (s : Arboreal I) (p : I→C.book.Token)
    (h : ℕ) {d : (↑s.leaves : Type)→ℕ} (v : Labels S d) (w : Labels S g)
    (hp : crop p s.leaves = names v) {M η c : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) :
    ∃ (k : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ) (y : J→E4),
      t s.root = r → s.Convoy M η t x → ClearOf (x s.root) y c →
      ‖algebraError F Q (crop x s.leaves) (x s.root) v y w h‖ ≤ A * s.listPrice p t (h+1) k ∧
      ∀ q : Viewers F, ‖formula F Q (crop x s.leaves) (x s.root) v y w h q‖ ≤ A * s.listPrice p t (h+1) k :=
  original F Q fac.toServices (tickets_suffice F fac hu ticket Q.spans) s p h v w hp hM hη hc

end YM.Integration.WilsonSharpPhysicalTreeDetectorSpectators
