import YM.Integration.WilsonGraphPaperCorrelations
import YM.Integration.WilsonCenteredNestedElection
import YM.OPE.Nesting.Geometry

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonSharpPhysicalTreeGeometryElection
open OPE OPE.Orbits OPE.Log Spec Filter PhysMS Answer.ContinuumLimit Answer.ContinuumLimit.PreElectedPublication
open WilsonGraphPaperPublication
open scoped Classical Topology

/-- The published pick already contains the matrix for this reader and the Foundation on the same Final. -/
theorem retained (g : YangMills.GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p) :
    let ξ := ElectedPublication.order p hp
    let E := construction.{u} g hg
    let V := publicPick.{u} g hg ξ
    (((issued.{u}).runs g hg).refine p hp).hierarchy = YangMills.hierarchy V.pupil.last V.pupil.P ∧
    V.pupil.f = ξ.refine V.g ∧ Facilities E.paths.family V.pupil.f V.pupil.S ∧
    Foundation V.pupil.last V.pupil.P ∧
    (V.pupil.Y : Filter (ℕ × ℕ)) ≤ V.pupil.f.fuse ∧
    MatrixTicket (C := E.paths.family) V.pupil.S V.pupil.last.sector.derivatives (V.pupil.Y : Filter _) ∧
    Nesting.Uniform V.pupil.last V.pupil.P ∧ LogTrace V.pupil.last V.pupil.P.port := by
  let ξ := ElectedPublication.order p hp
  let E := construction.{u} g hg
  let V := publicPick.{u} g hg ξ
  have h : Retained E (fun _ => True) ξ V :=
    (((rowBefore.{u} g hg).choose_spec.2.2 (fun _ => True) (fun _ _ _ => True.intro)).choose_spec.1) ξ
  have on_order : (V.pupil.Y : Filter (ℕ × ℕ)) ≤ V.pupil.f.fuse := V.usesP.symm ▸ h.1
  exact ⟨rfl, V.usesP, V.pupil.pillar, V.pupil.foundation, on_order, h.2.2.1,
    WilsonCenteredNestedElection.on_ticket E.paths V.pupil.last V.pupil.P V.pupil.pillar
      V.pupil.Y on_order h.2.2.1⟩

/-- The original recursive geometry admits a strict positive ratio cap, uniformly over every scale array. -/
theorem recursive (t : Nesting.Tree) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ C β : ℝ, 0 ≤ C ∧ β ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (s : t.Inner → ℝ) (z : t.Positions → E4) (r : ℝ), t.Tapered r β s →
        Nesting.Tree.Immediate M η t s z → Nesting.Tree.Relative C (η/2) t s z := by
  obtain ⟨C, β, hC, hβ, convert⟩ := t.of_immediate M η hM hη
  refine ⟨C, min β (1/2), hC, ⟨lt_min hβ.1 (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩, ?_⟩
  intro s z r hs hz
  exact convert s z r (hs.mono (min_le_left _ _) le_rfl) hz

end YM.Integration.WilsonSharpPhysicalTreeGeometryElection
