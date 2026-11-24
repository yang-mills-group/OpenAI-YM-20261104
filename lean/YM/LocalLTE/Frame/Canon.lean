import YM.LocalLTE.Inset.Harmony
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Views
/-! Canonical-frame local Taylor lifting (full torus recipe for AUX kernels only).
For local stencil use `Slide.shape` to choose MUCH smaller AUX kernel. Don't
read this as all W in physical torus, nor permission to erase called paths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Frame
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L c f : Side} {S : StepData c f} (T : Tube G S) (B : BudgetPoint) {β p σ C Λ : ℝ}
    {P : Teller G} (hP : Intake P T p (Pane.virgin T B β)) (hT:T.down.Bounds T.low σ C Λ)
local notation "E" => Positions (Uniform.Primary c G)

-- one orientation suffices, labels later moved under s∈ Signed
-- recipe: take short lifted path from 0 to every site, gauge that
-- transporter to identity, retain residual global colour at base 0.
def root (V : Config G c) := gauge (carrier 0 V) V
lemma color (z : Site c→G.El) (V:Config G c): root (gauge z V) = gauge (fun _=> z 0) (root V):= by
  have he i : SliceRows.carrier 0 (gauge z V) i=z 0 * SliceRows.carrier 0 V i * (z i)⁻¹ := by unfold SliceRows.carrier; rw [travel_gauge,SliceRows.deposits]
  funext i; unfold root; change carrier 0 (gauge z V) i.1*(z i.1*V i*(z (i.1+step i.2))⁻¹)*(carrier 0 (gauge z V) _)⁻¹=z 0 * (carrier 0 V i.1*V i*(carrier 0 V (i.1+step i.2))⁻¹)*(z 0)⁻¹; rw [he,he]
  group

-- frozen global adjoint colour relabel. Only polyn cost (constant indep c)
def adj (u:G.El) : Positions (Uniform.Primary c G)→L[ℝ] Positions (Uniform.Primary c G) :=
  (Uniform.tint G _).symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi (fun i=> (G.adjoint u).toContinuousLinearMap ∘L ContinuousLinearMap.proj i)) ∘L (tint G _).toContinuousLinearMap
lemma adj_label (u:G.El)(x:E): tint G _ (adj u x)=fun i=>G.adjoint u (tint G _ x i):= by unfold adj; ext; simp
lemma adj_mul (u v:G.El) (x:E): adj (u*v) x=adj u (adj v x):= (Uniform.tint G _).injective (by rw [adj_label,adj_label,adj_label]; exact funext fun i=> G.adjoint_mul ..)
lemma adj_bound (u:G.El) : ‖adj (c:=c) u‖ ≤ Uniform.shade G:= by
  refine ContinuousLinearMap.opNorm_le_bound _ (Uniform.shade_pos _).le fun x => ?_
  rw [show adj u x=(tint G _).symm (fun i=>G.adjoint u (tint G _ x i)) from rfl]
  · apply (tint_inv_le _).trans ((pi_norm_le_iff_of_nonneg (mul_nonneg (Uniform.shade_pos _).le (norm_nonneg _))).2 ?_); intro i; rw [norm_adjoint]; exact (norm_le_pi_norm _ _).trans (Uniform.tint_le x)
@[fun_prop] lemma adj_el (x:E): Continuous (fun u:G.El=>adj u x):= by
  let a (u:G.El) (i:Exterior.Body 1 c) := G.adjoint u (tint G _ x i)
  have he: Continuous a:= continuous_pi fun i=>
    G.projectColor.continuous_of_finiteDimensional.comp (f:=fun u=> G.conjugate u (G.colorMat (tint G _ x i))) (by unfold Gauge.conjugate; fun_prop)
  exact (Uniform.tint G _).symm.continuous.comp he

-- finite books put under global χ damping per link. No such model
-- mask needed on true push: only for comparison terms. (Color-projection
-- commutes even off compacts by explicit average.)
def convertLinks (χ:Chi) (d:ℝ) (u:G.El) (V:Config G c) : Positions (Uniform.Primary c G) :=
  (tint G _).symm (SliceRows.toLog fun i:Bond c=> cutLog χ d (gauge (fun _=>u) (root V) i))
def momentRead (U:E→ℝ) (x:E) := ∫ u:G.El,U (adj u x) ∂G.probHaar
def placed (χ:Chi)(d:ℝ)(U:E→ℝ) (V : Config G c) := momentRead U (convertLinks χ d 1 V)
variable {χ:Chi} {K Q r D d₀: ℝ}
lemma motion (h:Reliable G d₀ K) (z:G.El)(x:G.El)(V:Config G c):
    convertLinks χ d₀ (x*z) V= adj x (convertLinks χ d₀ z V) := by
  apply (tint G _).injective
  rw [adj_label]
  unfold convertLinks; rw [ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]; funext i
  exact (congr_arg (cutLog χ d₀) (by unfold Lattice.gauge; group : gauge (fun _=>x*z) (root V) ((Work.E03.poleEquiv c).symm i) = _)).trans (h.conjugate _ _ _)
lemma colorRead (h:Reliable G d₀ K) (z:Site c→G.El)(V:Config G c):
    convertLinks χ d₀ 1 (gauge z V) = adj (z 0) (convertLinks χ d₀ 1 V) := by
  rw [← motion h (x:=z 0),mul_one]; unfold convertLinks; rw [color]; simp [Lattice.gauge]
lemma invariant (h : Reliable G d₀ K)(f : E→ℝ): GaugeInvariant (placed χ d₀ f):= by
  intro x y; unfold placed momentRead; rw [colorRead h]; simp_rw [← adj_mul]; exact integral_mul_right_eq_self (μ:=G.probHaar) (fun i=>f (adj i (convertLinks χ d₀ 1 y))) _
lemma meansRead (h : Reliable G d₀ K)(f:E→ℝ)(V:Config G c): placed χ d₀ f V=∫ u:G.El, f (convertLinks χ d₀ u V) ∂G.probHaar:= by
  unfold placed momentRead; simp_rw [← motion h, mul_one]

include hT hP
lemma inherent (α : ℝ) : GaugeInvariant (Token.arrayE T B β α) := by
  let K:= Pane.virgin T B β; have hc:= hP.ready.knobs.symm ▸ hP.ready.kernel
  intro z V; unfold Token.arrayE
  have hu : S.push β (K.eval) (gauge z V)=S.push β K.eval V := by
    let F:= K.eval; let u:= z ∘ S.ratio.parent
    have hR := prior_gauge u
    let i (U) := S.density β U (gauge z V) • F U
    have hp : Integrable i (prior G _) := StepData.push_slice (S.isKernel hc β) _ _ (Rep.envelope _ hP.cap|>.integrable _)
    have hg := integral_map (μ:=prior G _) (f:=i) hR.aemeasurable
      (show AEStronglyMeasurable i _ from hR.map_eq.symm ▸ hp.aestronglyMeasurable)
    rw [hR.map_eq] at hg
    change (∫ U,i U ∂prior G _)=_
    rw [hg]; unfold StepData.push; apply integral_congr_ae; filter_upwards with U
    have hx:= S.covary hc u β U V; rw [show u ∘ S.ratio.embed=z from (funext fun x=> by simp [u,S.ratio.embed_parent])] at hx
    exact congr_arg₂ (fun a b : ℝ=>a*b) hx (lawful_gi hP.cap u U)
  have hx := Work.F05.mainTerm_gauge hT V z
  have hp: secondTerm T.low T.down (gauge z V)= secondTerm T.low T.down V:= by simp only [secondTerm,Work.F05.pull_gauge_zero,Work.F05.quadratic_gauge hT]
  rw [hx,hp,Work.F05.loop_gauge hT,hu]
end YM.LocalLTE.Frame
