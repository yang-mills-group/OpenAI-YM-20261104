import YM.Integration.WilsonPositionProgramSharedInversionTariff
import YM.Integration.WilsonPositionProgramFilmGroundFigure

/-! The finite chronological Wilson inversion bank may be tested at varying
public measuring vectors. All angular degrees share the same original-period
threshold after the independent site, tree, and stopping date have been set. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicFiniteInversion
open Exterior Wilson Tree RegulatorIR.Binding Function Filter Finset Set Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open RegulatorIR.Diagram.Formal RegulatorIR.FVAAlt2.Kick
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSeriesRead WilsonPositionProgramInversionMaterial
open WilsonPositionProgramSubmittedGeometry WilsonPositionProgramVariableCircuit
open scoped Classical Topology ENNReal BigOperators PowerSeries

variable {G:Gauge} (C:Run G) (D:XSpace.Run) {X:Type} (m j:X→ℕ) (w:X→ℕ→ℕ)
  (blocks:∀x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
  (branch:∀P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
variable {I:Type} [Fintype I] [LinearOrder I] (F:Tent j) (sites:X→I → Cover)
  (d:I→ℕ) (x:X) (q:ℕ)

def observed (per:ℕ) (u:Terms C d q):ℂ :=
  Booth.Uniforms.cuff (See.observe branch K H (Sound.Figure.prop C sites d (axis C d u.1))
    (sheet F) per ((final j).choose x)) (Kick.depthF univ d (axis C d u.1)) u.2.val.2 0

def terminal (u:Terms C d q):ℂ :=
  (Rocket.stopped E Y branch F (Lodge.basisR C) univ d (axis C d u.1)
    (final j) sites x u.2.val.2:ℝ)

theorem printed (u:Terms C d q):
    Tendsto (fun per=>observed C D m j w blocks branch F sites d x q per u) atTop
      (𝓝 (terminal C D m j w blocks branch F sites d x q u)):=by
  have lim:=Sound.Figure.green C branch Y H sites F (final j) x d (axis C d u.1) u.2.val.2
  simp only [Sound.Figure.innerV,Sound.Figure.perRead,Sound.money,PowerSeries.coeff_mk] at lim
  apply lim.congr'
  filter_upwards with per
  unfold observed Booth.Uniforms.cuff
  rw [Binding.flavor_lo,show FreeResolvent.flatten (0:fieldDir G _ 1)=0 from rfl,←Prim.speaking,Prim.starts]
  rfl

/-- The original period threshold is chosen before all numerical vectors.
Its fee is the single total variation of their actual antidiagonal. -/
theorem original (ε:ℝ) (pos:0<ε):
    ∀ᶠ per:ℕ in atTop,∀ a:Terms C d q→ℂ,
    ‖(∑u,a u*observed C D m j w blocks branch F sites d x q per u)-
      ∑u,a u*terminal C D m j w blocks branch F sites d x q u‖ ≤
        ε*∑u,‖a u‖:=by
  have allTerms:∀ᶠ per:ℕ in atTop,∀u:Terms C d q,
      dist (observed C D m j w blocks branch F sites d x q per u)
        (terminal C D m j w blocks branch F sites d x q u)<ε:=
    Filter.eventually_all.2 fun u=>Metric.tendsto_nhds.mp
      (printed C D m j w blocks branch F sites d x q u) ε pos
  filter_upwards [allTerms] with per cmp a
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  simp_rw [←mul_sub]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro u _
  rw [norm_mul,mul_comm ε]
  exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (cmp u).le) (norm_nonneg _)

end YM.Integration.WilsonOriginalPublicFiniteInversion
end
