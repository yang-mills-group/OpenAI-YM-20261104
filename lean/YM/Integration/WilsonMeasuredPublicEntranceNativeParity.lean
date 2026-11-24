import YM.Integration.WilsonMeasuredPublicEntranceNativeFrame
import YM.Integration.WilsonMovingForkReporterBraided

/-! A single chart is chosen at each original radius before the two sequences.
On every subsequently joined physical extraction both chart changes are exactly
the identity on each fixed witnessed grade. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeParity
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE Spin
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Further.CorrectedLift
open WilsonMeasuredPublicEntranceNativeFrame WilsonMovingForkReporterBraided
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (ℓ:Ultrafilter (ℕ×ℕ)){radius:ℝ}(horizon:Set.Ioc (0:ℝ) radius→ℕ)
    (survey:∀s,Vane C (horizon s))(fallback:ℝ→tower S)
    (outer inner:ℕ→Set.Ioc (0:ℝ) radius)
    (chosen:Pair (fun i=>survey (outer i)) (fun i=>survey (inner i)))
    {J:Scaling S}{H:(Cells.standard C).Hierarchy}
    {Y:∀d:ℕ,ℕ→(Cells.standard C).Field d→L[ℂ] C.label d}

theorem original (income:Gondola f H J ℓ chosen.report Y)(d:ℕ):
    ∀ᶠ i:ℕ in atTop,
      atRadius ℓ horizon survey fallback (outer (chosen.pick i)).val d=J.U (2*i) d ∧
      atRadius ℓ horizon survey fallback (inner (chosen.pick i)).val d=J.U (2*i+1) d:=by
  obtain ⟨start,paid⟩:=eventually_atTop.mp (income.terminal d)
  filter_upwards [eventually_ge_atTop (start+d)] with i large
  have hi:d≤2*i:=by omega
  have ho:d≤2*i+1:=by omega
  constructor
  · apply at_site ℓ horizon survey fallback _ (hi.trans (chosen.outer i))
    have source:(fun p=>(survey (outer (chosen.pick i))).wheel.atCut p
        ⟨d,Nat.lt_succ_of_le (hi.trans (chosen.outer i))⟩)=heightV chosen.report (2*i) d:=by
      funext p
      rw [heightV,dif_pos hi,even]
      rfl
    rw [source]
    exact ⟨Y d (2*i),paid _ (by omega)⟩
  · apply at_site ℓ horizon survey fallback _ (ho.trans (chosen.inner i))
    have source:(fun p=>(survey (inner (chosen.pick i))).wheel.atCut p
        ⟨d,Nat.lt_succ_of_le (ho.trans (chosen.inner i))⟩)=heightV chosen.report (2*i+1) d:=by
      funext p
      rw [heightV,dif_pos ho,odd]
      rfl
    rw [source]
    exact ⟨Y d (2*i+1),paid _ (by omega)⟩

end YM.Integration.WilsonMeasuredPublicEntranceNativeParity
end
