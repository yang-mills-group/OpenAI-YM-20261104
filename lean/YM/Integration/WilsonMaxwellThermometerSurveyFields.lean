import YM.Integration.WilsonMaxwellThermometerSurveyBirth
import YM.Integration.WilsonPositionProgramInvertedStencil
/-! A public prepared real basis word on its own finite group field, before normalization or either limit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonMaxwellThermometerSurveyFields
open Set Filter Function Finset Matrix RG Lattice PhysicalNext.Repeat.Legato Source
open Precision Wilson XSpace RegulatorIR.FVAAlt2 PertExtension
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank PertExtension.Orb
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {p : Period} (T : p.Tree)

open WilsonPositionProgramInvertedStencil (packet tangent coordinates)
open WilsonMaxwellThermometerSurveyIncome (master chapter)
def moved (W : Initialize G) (d : ℕ) (u : ((primes G).F d).Index) (z : Cover) :
    Lawn (Woods G p.side) → ℝ := fun v => Plies (chapter W d) u p.side
      (Matrix.mulVec (spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side)) v)

theorem curved (W : Initialize G) (d : ℕ) (u : ((primes G).F d).Index) (z : Cover) :
    Green (moved (p:=p) W d u z) := by
  let m := spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side)
  have origin : m *ᵥ (0:Lawn (Woods G p.side)) = 0 := Matrix.mulVec_zero m
  have h : ContDiffAt ℝ ω (Plies (chapter W d) u p.side) (m *ᵥ 0) := by
    rw [origin]
    exact innu _ (Next.Foundations.hol G) ((master W).spec d) u p.side
  exact h.comp 0 (board m)

theorem submitted (W : Initialize G) (d : ℕ) (u : ((primes G).F d).Index) (z : Cover) (v : T.Field G) :
    moved W d u z (tangent T v) =
      SlotEvaluation.fieldAt (chapter W d) u (wrap p.side z) (T.links v) := by
  change ((chapter W d).places (Pi.single u 1) 0 (mantle (_ *ᵥ tangent T v))).re = _
  rw [mantle_reads, Lattice.pull_one,coordinates,SectionData.places_trans,zero_add]
  rfl

theorem original (W : Initialize G) (d : ℕ) (u : ((primes G).F d).Index) (z : Cover) :
    packet T (loom (spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side))
      (jet (Plies (chapter W d) u p.side))) =
      Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
        (SlotEvaluation.fieldAt (chapter W d) u (wrap p.side z) ∘ T.links)) := by
  let K := spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side)
  let f := Plies (chapter W d) u p.side
  have hf : Green f := innu (chapter W d) (Next.Foundations.hol G) ((master W).spec d) u p.side
  change packet T (loom K (jet f)) = _
  rw [loom_jet K f hf]
  change packet T (jet (moved W d u z)) = _
  have matchf : moved W d u z ∘ tangent T = SlotEvaluation.fieldAt (chapter W d) u (wrap p.side z) ∘ T.links :=
    funext fun x => submitted T W d u z x
  rw [packet,WilsonPositionProgramRayChart.original _ _ _ (curved W d u z),matchf]



theorem literal (W : Initialize G) (d : ℕ) (u : ((primes G).F d).Index) (z : Cover) :
    packet T (loom (spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side))
      (jet (Plies (chapter W d) u p.side))) =
      Taylor.expandTaylor (T.basis G) (fun v=>(chapter W d).places (Pi.single u 1) (wrap p.side z) (T.links v)) := by
  rw [original]
  apply congrArg (Taylor.expandTaylor (T.basis G))
  funext v
  exact SlotEvaluation.scalar_real ((master W).spec d)

end YM.Integration.WilsonMaxwellThermometerSurveyFields
end
