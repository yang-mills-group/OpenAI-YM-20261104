import YM.Integration.WilsonOriginalPublicFiniteInversion
import YM.Integration.WilsonOriginalPublicTrialNormalization

/-! At a fixed public test and stage, a single independent period is chosen for
all words before the numerical coefficients of the physical trial are supplied. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicFigurePeriod
open Exterior Wilson Tree RegulatorIR.Binding Function Filter Finset Set Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open RegulatorIR.Diagram.Formal RegulatorIR.FVAAlt2.Kick
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSubmittedGeometry WilsonPositionProgramVariableCircuit
open scoped Classical Topology ENNReal BigOperators PowerSeries
variable {G:Gauge}(C:Run G)(D:XSpace.Run){X:Type}(m j:X→ℕ)(w:X→ℕ→ℕ)
    (blocks:∀x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
    (branch:∀P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
variable {I:Type}[Fintype I][LinearOrder I](F:Tent j)(sites:X→I→ Cover)(d:I→ℕ)(x:X)
local notation "B" => (∀i,(C.family.labels.level (d i)).Index)
def source (per q:ℕ)(a:B):ℂ:=
  Booth.Uniforms.cuff (See.observe branch K H (Sound.Figure.prop C sites d a)
    (sheet F) per ((final j).choose x)) (Kick.depthF univ d a) q 0
def stopped (q:ℕ)(a:B):ℂ:=
  (Rocket.stopped E Y branch F (Lodge.basisR C) univ d a (final j) sites x q:ℝ)

theorem convergence (q:ℕ)(a:B):
    Tendsto (fun per=>source C D m j w blocks branch F sites d x per q a) atTop
      (𝓝 (stopped C D m j w blocks branch F sites d x q a)):=by
  have lim:=Sound.Figure.green C branch Y H sites F (final j) x d a q
  simp only [Sound.Figure.innerV,Sound.Figure.perRead,Sound.money,PowerSeries.coeff_mk] at lim
  apply lim.congr'
  filter_upwards with per
  unfold source Booth.Uniforms.cuff
  rw [Binding.flavor_lo,show FreeResolvent.flatten (0:fieldDir G _ 1)=0 from rfl,←Prim.speaking,Prim.starts]
  rfl

def shifted (q:ℕ)(a:B)(f:ℕ→ B→ℂ):ℂ:=
  if Kick.depthF univ d a≤q then f (q-Kick.depthF univ d a) a else 0

theorem purchased (q:ℕ)(δ:ℝ)(pos:0<δ):
    ∀ᶠ per in atTop, ∀a:B,
      ‖shifted C d q a (source C D m j w blocks branch F sites d x per)-
        shifted C d q a (stopped C D m j w blocks branch F sites d x)‖ₑ≤ENNReal.ofReal δ:=by
  apply Filter.eventually_all.mpr
  intro a
  by_cases reaches:Kick.depthF univ d a≤q
  · simp only [shifted,if_pos reaches]
    have close:=Metric.tendsto_nhds.mp (convergence C D m j w blocks branch F sites d x
      (q-Kick.depthF univ d a) a) δ pos
    filter_upwards [close] with per hp
    exact (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hp.le))
  · simp [shifted,reaches]

theorem tested (A:B→ℂ)(B₁ B₂:B→ℂ)(ε δ:ℝ≥0∞)
    (former:∀a,‖A a-B₁ a‖ₑ≤ε)(latter:∀a,‖B₂ a-B₁ a‖ₑ≤δ)(c:B→ℂ):
    ‖(∑a,c a*A a)-(∑a,c a*B₂ a)‖ₑ≤(ε+δ)*∑a,‖c a‖ₑ:=by
  rw [←sum_sub_distrib,mul_sum]
  refine (enorm_sum_le ..).trans (sum_le_sum fun a _=>?_ )
  rw [←mul_sub,enorm_mul,mul_comm (ε+δ)]
  gcongr
  rw [←edist_eq_enorm_sub]
  refine (edist_triangle _ (B₁ a) _).trans (add_le_add ?_ ?_)
  · simpa only [edist_eq_enorm_sub] using former a
  · simpa only [edist_comm (B₁ a) (B₂ a),edist_eq_enorm_sub] using latter a

end YM.Integration.WilsonOriginalPublicFigurePeriod
end
