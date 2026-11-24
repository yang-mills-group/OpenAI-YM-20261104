import YangMills.WilsonProof.Hierarchy
import YangMills.VacuumReconstruction
import YM.EveryPhase.Implement

noncomputable section
set_option autoImplicit false
namespace YangMills.WilsonProof.PhaseAwards

open YM YM.Spec YM.OPE.Orbits YM.Boundary YM.Mink YM.EveryPhase YM.EveryPhase.Stress
open YM.Next.BOUNDARY.Descent YangMills.Reconstruction
open MeasureTheory Set
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable {F : Final C o S} (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (L : Almanac F)

private theorem matrix_eq (p : ProperLorentz) : lorentzMatrix p = mat p := by
  funext a b
  exact (entry (Lorentz.act p) a b).symm

private theorem partial_value (a : Axis) (m : TestFunction) (x : Spacetime) :
    partialProbe a m x = -Maxwell.partialD a (fun y => m y) x := by
  change -(_) = -(_)
  exact congrArg Neg.neg (SchwartzMap.lineDerivOp_apply_eq_fderiv ..)

theorem continuedStress (i : F.α.space.X) :
    ContinuedStress (hierarchy F Q) (view (L.actors i)) := by
  classical
  let A := L.actors i
  have award := YM.EveryPhase.Stress.force L i
  have letters := (L.cores i).letters
  refine ⟨award.symmetric, ?_, ?_, ?_⟩
  · intro p a b
    change A.spin.rail p.Λ (S.pin 4 (M F.sector.energy a b)) =
      ∑ u, ∑ v, (((lorentzMatrix p.Λ u a * lorentzMatrix p.Λ v b : ℝ) : ℂ)) •
        S.pin 4 (M F.sector.energy u v)
    rw [letters.ties, transform_M F.sector.energy F.phase.transport.spots F.phase.transport.spin letters,
      matrix_eq]
    simp only [column, map_sum, map_smul]
  · intro b m
    exact ⟨fun a => partialProbe a m, fun a x => partial_value a m x, award.conserve b m⟩
  intro d B γ h0 V hV t
  simp only [matrix_eq] at hV
  obtain ⟨tangentV, deriv⟩ := rank_derivative F.phase.transport.spots A.spin letters d
    (c := γ) (Subtype.ext h0) hV B
  let K : Killing := ⟨t, V, tangentV⟩
  have velocity (x : Spacetime) (a : Axis) : K.realV x a = affineVelocity t V x a := by
    simp only [Killing.realV, PiLp.add_apply, M4.at_coord, affineVelocity, K]
  refine ⟨fun τ => A.spin.shell d (γ τ) B, rankAction F.sector.turns d V B,
    fun τ => (letters.ties (γ τ) d B).symm, deriv, ?_⟩
  intro X compact f hf realF unit c hc clearance m hm
  obtain ⟨o, R, positive, plateau, clear⟩ := clearance
  have reserve : Reservation X f c := by
    refine ⟨hc, o, R, positive, plateau, ?_⟩
    intro s hs y hy z hz
    apply clear (YM.position y s) _ _ z hz
    · change YM.time (YM.position y s) ∈ tsupport f
      rwa [YM.time_position]
    · change YM.spatial (YM.position y s) ∉ Metric.ball o R
      rwa [YM.spatial_position]
  refine ⟨fun a => touch K a (pincushion c f), fun a => partialProbe a (touch K a m),
    fun a x => ?_, fun a x => ?_, award.commutator X compact f ⟨realF, hf, unit⟩ c reserve ⟨d, B⟩ m hm K⟩
  · rw [touch_at, pincushion_at, velocity]
    rfl
  · rw [partial_value]
    congr 1
    apply congrArg (fun h : Spacetime → ℂ => Maxwell.partialD a h x)
    funext y
    rw [touch_at, velocity]

end YangMills.WilsonProof.PhaseAwards
