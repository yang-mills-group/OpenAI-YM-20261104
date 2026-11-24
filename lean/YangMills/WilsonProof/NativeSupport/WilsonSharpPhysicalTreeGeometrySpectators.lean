import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryPrices
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryReader
import YM.Integration.WilsonSharpPhysicalTreeDetectorApplication

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open Function Filter Finset Set YangMills.Hierarchy OPE OPE.Orbits OPE.Orbits.Reader OPE.Arboreal Spec
open scoped Classical BigOperators Topology

variable {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- The published spectator expression has the sharp through-h tree price on the same physical reader. -/
theorem spectator_remainder_from (tested : WilsonSharpPhysicalTreeDetectorApplication.AllTrees F Q)
    (t : FusionTree) (a : Fin t.leaves → S.Tag) {J : Type} [Fintype J] (b : J → S.Tag)
    (h : ℕ) (o : E4) (M η c : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c)
    (K : Set (J → E4)) (clear : ∀ y ∈ K, YangMills.Hierarchy.Clear o y c) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0,
      ∀ s x z, t.Admissible r β M η s x z → z 0 = o → ∀ y ∈ K, ∀ q,
        ‖(YangMills.hierarchy F Q).grouped q a x b y -
          (YangMills.hierarchy F Q).truncatedWithSpectators h q a x o b y‖ ≤
          A * t.bound (YangMills.hierarchy F Q) ((h : ℝ)+1) a s k := by
  let T := rawTree t
  let P := rawTokens t a
  let A := rawTags t a
  obtain ⟨k, C₀, hC, row⟩ := tested (Node t) J T P h (fun i => (A i).1) (fun j => (b j).1)
    (fun i => (A i).2) (fun j => (b j).2) (rawTokens_names t a) M (η/2) c hM (half_pos hη) hc
  refine ⟨ratioCap t M η, ratioCap_mem t hM hη, C₀ + 1, by linarith, k, ?_⟩
  filter_upwards [row, (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))] with r buy hr
  intro s x z ad eq y hy q
  replace ad : ImmediateCourt t r (ratioCap t M η) M η s x z := ad.2
  let R := rawScale t s
  let X := rawPosition t x z
  have geometry : T.Convoy M (η/2) R X := convoy hM hη ad
  have wall : ClearOf (X T.root) y c := by change ClearOf (z 0) y c; rw [eq]; exact ⟨(clear y hy).1, (clear y hy).2⟩
  have bought := buy X R y ad.1 geometry wall
  have small (v : t.Vertex) : 0 < s v ∧ s v ≤ 1 :=
    ⟨ad.2.1 v, ((geometry.sizes.bound (T.closure (.inl v)) (zone_inl t v)).trans_eq ad.1).trans hr.2.le⟩
  have price : T.listPrice P R (h+1) k = t.bound (YangMills.hierarchy F Q) ((h:ℝ)+1) a s k := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      listPrice_eq t (YangMills.hierarchy F Q) P a (rawTokens_grade t a) (h+1) k s small
  have nonnegative : 0 ≤ T.listPrice P R (h+1) k := by
    unfold OPE.Arboreal.listPrice
    apply mul_nonneg (geometry.sizes.worth (h+1) P T.initial).le
    rw [prestige_eq t s small k]
    exact prod_nonneg (fun _ _ => by positivity)
  rw [←eq, public_formula F Q t q a x z b y h bought.1, ←price]
  exact (bought.2.2.2 q).trans (mul_le_mul_of_nonneg_right (by linarith) nonnegative)

theorem spectator_remainder (paid : Services C f S) (trace : LogTrace F Q.port)
    (t : FusionTree) (a : Fin t.leaves → S.Tag) {J : Type} [Fintype J] (b : J → S.Tag)
    (h : ℕ) (o : E4) (M η c : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c)
    (K : Set (J → E4)) (clear : ∀ y ∈ K, YangMills.Hierarchy.Clear o y c) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0,
      ∀ s x z, t.Admissible r β M η s x z → z 0 = o → ∀ y ∈ K, ∀ q,
        ‖(YangMills.hierarchy F Q).grouped q a x b y -
          (YangMills.hierarchy F Q).truncatedWithSpectators h q a x o b y‖ ≤
          A * t.bound (YangMills.hierarchy F Q) ((h : ℝ)+1) a s k :=
  spectator_remainder_from F Q (WilsonSharpPhysicalTreeDetectorApplication.same_reader F Q paid trace)
    t a b h o M η c hM hη hc K clear

end YM.Integration.WilsonSharpPhysicalTreeGeometry
