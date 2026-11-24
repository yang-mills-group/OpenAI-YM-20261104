import YM.Integration.WilsonMacroscopicPrescribedInputs
import YM.Pier.Blocks.Plate

/-! Directional differentiation keeps the reporting radius and the measured
field fixed. The original compact displacement receipt prices the whole
two-site derivative before its second field is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicSpatialDerivatives
open Function Filter Finset Set MeasureTheory Extraction Table
open Spec Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {V : Table C.book}
variable {n : ℕ}

/-- No running field or cutoff is differentiated. -/
theorem at_slot (F : Spec.Final C f V) (q : Viewers F) (t : Fin n → V.Tag)
    {r : ℝ} (hr : 0<r) {x : Points n} (hx : x∈conf n) (i : Fin n) (a : Axis) :
    Points.gradient i a (fun y : Points n=>V.useAt (spectator F q) (r • y) t) x =
    r • V.useAt (spectator F q) (r • x) (Function.update t i
      ⟨(t i).1+1,F.sector.derivatives.deriv (t i).1 a (t i).2⟩) := by
  let v (z : Points n) := V.useAt (spectator F q) z t
  have h := Work.A05.smul_conf hr hx
  have smooth : DifferentiableAt ℝ v (r • x) :=
    ((V.class_smooth _ (spectate F q).smooth t).contDiffAt ((conf_open _).mem_nhds h)).differentiableAt (by simp)
  have actual := F.sector.derivatives.derivative_slot (spectate_evolution F q) (spectate F q).laws.toSymmetric
    (spectate F q).smooth h i t (t i).2 a
  rw [show update t i (⟨(t i).1,(t i).2⟩ : V.Tag)=t from update_eq_self ..] at actual
  exact (Work.A04.gradient_scaled r v x smooth i a).trans (congrArg (fun z : ℂ=>r • z) actual.symm)

/-- Uniform, including for the reflected field subsequently chosen to be the
unknown descendant itself. -/
theorem compact (F : Spec.Final C f V) (J : ℝ → PhysMS.tower V) (P : Pier.Lair.Present F J)
    (d : Caps n) (K : Set (Points n)) (hk : IsCompact K) (sep : K⊆conf n) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ r in Trace.Pilot.trail,∀ x∈K,∀ v : (j:Fin n)→RG17.Free C (d j),
      ‖fderiv ℝ (fun y : Points n=>V.classMoment V d (r • y) (fun j=>J r (d j) (v j))) x‖ ≤
        M*(∏ j : Fin n,‖v j‖) := by
  obtain ⟨M,c,hM,hc,buy⟩ := P.confines d K hk sep
  refine ⟨M,hM,?_⟩
  filter_upwards [buy] with r paid x inside v
  apply norm_fderiv_le_of_lip' ℝ (mul_nonneg hM.le (Finset.prod_nonneg fun _ _=>norm_nonneg _))
  filter_upwards [Metric.ball_mem_nhds x hc] with y hy
  exact (paid x inside y (by simpa only [Metric.mem_ball,dist_eq_norm] using hy.le)).2 v

end YM.Integration.WilsonMacroscopicSpatialDerivatives
