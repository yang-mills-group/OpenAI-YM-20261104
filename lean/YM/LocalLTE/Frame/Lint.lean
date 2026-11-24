import YM.LocalLTE.Frame.Slew
/-! Regularity of full-group Taylor prediction. Does not price it at non-
contractible holonomies. Keeps smoothness at every mask (all V).
 `Proper` not continuity only on interiors. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Frame
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L c f : Side} {j n : ℕ} {a Y d₀ d v q p : ℝ}
local notation "E" => Positions (Uniform.Primary c G)
local notation "r" => Blaze.royalty G

lemma starAt {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U:X → Config G c} {x:X} (k:Bond c)
    (h:∀ k,ContDiffAt ℝ ∞ (fun y=> G.mat (U y k)) x) : ContDiffAt ℝ ∞ (fun y=> G.mat (root (U y) k)) x:= by
  have hh (l:Walk) (k:Site c): ContDiffAt ℝ ∞ (fun y=> G.mat (travel (U y) k l)) x:= by
    induction l generalizing k with
    | nil=> simp only [travel]; exact contDiffAt_const
    | cons i l ih=>
      simp only [travel,G.mat_mul]; apply ContDiffAt.mul ?_ (ih _); rcases i with ⟨_,b|b⟩
      · exact h _
      exact (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp x (h _)
  unfold root Lattice.gauge; simp only [G.mat_mul,G.mat_inv]
  exact ((hh _ _).mul (h _)).mul ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp x (hh _ _))
lemma incurred (V : Config G c) (k: Bond c) : ContDiffAt ℝ ∞ (fun y=> G.mat (root (increment V y) k)) 0:= starAt k fun i=> by
  unfold increment; simp only [G.mat_mul]; exact (((G.exp_jet.comp (contDiff_apply ..)|>.contDiffAt).of_le (by exact le_top)).mul contDiffAt_const)
lemma borel_root : Measurable (root (G:=G) (c:=c)):= by
  have h : Continuous (root (G:=G) (c:=c)) := continuous_pi fun i=> by unfold root SliceRows.carrier Lattice.gauge; fun_prop
  exact h.measurable
variable (P : BudgetPoint)
lemma momSmooth (f:E→ℝ) (hf:ContDiff ℝ (↑ j) f) : ContDiff ℝ (↑ j) (momentRead f):= by
  simp_rw [contDiff_iff_contDiffAt]; intro x
  let k:= ‖x‖+2; let Q:= Uniform.shade G; have hQ:0<Q:= Uniform.shade_pos G
  have hk :0<k:= by unfold k; positivity
  let g (x:E) i:= f (adj i x)
  obtain ⟨C,he,hC⟩:= Brush.compact (s:=Metric.closedBall 0 (Q*k)) (isCompact_closedBall _ _) (fun i _=> hf.contDiffAt (x:=i))
  have hV: ∀ᶠ y:E in 𝓝 x,‖y‖≤k := by filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (show ‖x‖<k from lt_add_of_pos_right ‖x‖ (by norm_num)))] with y hy using (show ‖y‖<k from hy).le
  have hp : ∀ᶠ y in 𝓝 x,∀ i,Brush j (C*(1+1*Q)^j) 1 (fun x=>g x i) y:=by
    filter_upwards [hV] with y hy i; exact (reading (adj i) (hC (adj i y) (mem_closedBall_zero_iff.mpr (((adj i).le_opNorm y).trans (mul_le_mul (adj_bound _) hy (norm_nonneg _) hQ.le)))) (adj_bound _)).trim
  obtain ⟨h,-⟩ := Meristem.points g G.probHaar ⟨fun _=>_, integrable_const _, hp⟩ (Eventually.of_forall (fun y=>(hf.continuous.comp (adj_el _)).measurable)); exact h.calls.1
lemma authorized (f : E→ℝ) {χ:Chi} (hs: Reliable G p q) (hf : ContDiff ℝ P.order f) : P.Regular univ (Frame.placed χ p f):=by
  let V : Config G c→ E := Frame.convertLinks χ p 1
  have he:Measurable V := by
    let Z (U:Config G c):= SliceRows.toLog fun i:Bond c=> cutLog χ p ((Frame.chainT 1 U) i)
    have hv : Measurable Z:= measurable_pi_lambda _ (fun i=> ?_)
    · exact (tint G _).symm.continuous.measurable.comp hv
    change Measurable (fun v:Config G c=> cutLog χ p (chainT 1 v ((Work.E03.poleEquiv c).symm i)))
    have hv (U : Config G c): Frame.chainT 1 U=root U:=funext fun i=> by simp [chainT,Lattice.gauge]
    simp_rw [hv]; exact (hs.borel χ).comp ((measurable_pi_apply ((Work.E03.poleEquiv c).symm i)).comp (borel_root (G:=G)))
  have hm (U:Config G c): Local.Chart P.order (placed χ p f) U:= by
    have ht:V ∘ increment U = fun k=> (Uniform.tint G _).symm (SliceRows.toLog fun i:Bond c=> cutLog χ p ((Frame.root (increment U k)) i)):=funext fun k=> congr_arg (tint G _).symm (by ext i; unfold Lattice.gauge; simp)
    change ContDiffAt ℝ _ ((Frame.momentRead f) ∘ V ∘ increment U) 0; rw [ht]
    let t x:=SliceRows.toLog (fun i:Bond c=> cutLog χ p (root (increment U x) i))
    change ContDiffAt ℝ (↑ P.order) ((Frame.momentRead f) ∘ ((tint G (Exterior.Body 1 c)).symm ∘ t)) 0
    refine (momSmooth f hf|>.contDiffAt).comp _ ((Uniform.tint G _).symm.contDiff.contDiffAt.comp _ (show ContDiffAt ℝ (↑ P.order) t 0 from ?_))
    refine contDiffAt_pi.mpr (fun i=>?_); exact (hs.smooth χ (incurred U ((Work.E03.poleEquiv c).symm i))).of_le (show (P.order : WithTop ℕ∞) ≤ (∞:WithTop ℕ∞) from (show (↑(P.order:ℕ∞):WithTop ℕ∞)≤ ↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top))
  refine ⟨fun U V hv=> ?_,(momSmooth f hf|>.continuous.measurable).comp he, Frame.invariant hs _,fun U _=> hm U,fun U _ A l hl=> Next.Foundations.left_has A hl (hm U)⟩
  congr 1; exact funext fun i=> hv i (by simp) (by simp)
end YM.LocalLTE.Frame
