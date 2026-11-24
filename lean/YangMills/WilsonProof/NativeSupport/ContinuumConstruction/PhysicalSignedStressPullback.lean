import YM.TraceExtension.Atlas.Energy
set_option maxHeartbeats 950000
set_option maxRecDepth 8192
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}{C:Family G}{X:Extraction.Order}{L:Register G}
variable {S:Table C.book}(F: Spec.Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
open StressFlux TraceExtension Over

theorem restaffedSignedEnergyPullback (r : ℝ) (P : change S 4)
    (axes : ∀ (s : Signed) (u : (Bel C.book).Field 4),
      P ((Bel C.book).mirror H.spin 4 s u) = S.mirror F.room.kernel.spin 4 s (P u)) :
    RawTensor H.spin (fun i j : Axis => P.symm (r^4 • F.sector.energy i j)) := by
  let R := F.sector.energy
  intro s a b
  apply P.injective
  rw [axes,LinearEquiv.apply_symm_apply,←F.phase.transport.spots.signed,map_sum]
  simp_rw [map_sum,map_smul,LinearEquiv.apply_symm_apply]
  let f := (F.sector.turns.act 4 s.ortho).toLinearMap.restrictScalars ℝ
  rw [show F.sector.turns.act 4 s.ortho (r^4 • R a b) = r^4 • F.sector.turns.act 4 s.ortho (R a b)
    from f.map_smul ..,F.phase.transport.spin]
  simp only [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm ..
end YM.Trace.Pilot
end
