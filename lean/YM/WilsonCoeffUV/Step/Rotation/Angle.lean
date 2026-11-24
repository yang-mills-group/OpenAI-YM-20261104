import YM.WilsonCoeffUV.Step.Rotation.Price
/-!
# Action equality including noise and ALL allowed predictors in the shared step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Freedom
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Work.F05 Function Filter Gauge PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)
variable {B T:Forest S.ratio}(e:B.Free≃T.Free)
variable (M M' : Matrix (Woods G f) (Woods G c) ℝ) (Q:Matrix (Body 1 f) (Body 1 c) ℝ)
local notation "ρ"=> reroll (path (U:=Woods G c)) (spool (internal S e M M'))
local notation "ℓ"=> beam S e (G:=G)
private abbrev hub:= Lawn (Active G B⊕Woods G c)

lemma pan_price (p:Ink (Woods G f))(ha:M=reveal G S B*((reveal G S B).transpose*M))(hb:M'=reveal G S T*((reveal G S T).transpose*M'))
   (h:rollTest p p 1 0) : loom (camSlice G S B M) p= ρ (loom ℓ (loom (camSlice G S T M') p)) := by
  have he:= h (pan_turn S e M M' ha hb)
  rw [windV,rolled_loom _ (expose_zero ..) (expose_green ..),← spool_loom]; exact he

lemma pan_angular (ha:M=reveal G S B*((reveal G S B).transpose*M))(hb:M'=reveal G S T*((reveal G S T).transpose*M'))(h:S.patch.Branches S.kernel G) :
   let p:=flash (sprig (jointPen G S) 2)
   loom (panSlice G S B M) p = ρ (loom ℓ (loom (panSlice G S T M') p)) := by
  intro p
  rw [windV,rolled_loom _ (expose_zero ..) (expose_green ..),← spool_loom]
  let k:=jointPen G S
  let g:=localPhi S (B:=B) T M
  let K:=panSlice G S T M'
  let R:=pan S e M M'; let V v:= K*ᵥ R v; let U v:= panSlice G S B M*ᵥ v
  have hz : (PowerSeries.X ^ 2)*p=jet k := sprouts_move (pen_jets G S h).1 (pen_jets G S h).2.1
  have hW:= pan_turn S e M M' ha hb
  have θ₀: Tendsto (fun u=>camSlice G S B M *ᵥ u) (𝓝 0) (𝓝 0) := hW.f₀ ▸ hW.g₀.continuousAt
  have θ₁: Tendsto (fun u=>camSlice G S T M' *ᵥ pan S e M M' u) (𝓝 0) (𝓝 0) := hW.f₁ ▸ hW.g₁.continuousAt
  have hr : S.ratio.embed (0:Site c)=0:= by simpa using S.ratio.embed_wrap 0
  have hs : ∀ᶠ v: hub (S:=S) (B:=B) (G:=G) in 𝓝 0,k (U v)=k (V v):= by
    filter_upwards [θ₀.eventually (penalty_same S h),θ₁.eventually (penalty_same S h), hW.shift] with w hv hh he
    apply price_channel S h (U w) (V w) 1 0 (g w)
    · unfold U V K; rw [arm_pan,arm_pan,hr]; exact he
    · unfold U V K; rw [arm_pan,arm_pan, pull_id,(pan_join S e M M' w).2]
      have hg: g w ∘ S.ratio.embed=fun _=>1 := funext fun i=> T.fold_root _ _
      rw [hg]; funext i; unfold Lattice.gauge; simp; rfl
    · unfold U; rw [arm_pan]; exact hv
    unfold V K; rw [arm_pan]; exact hh
  have hV: V 0=0:=by unfold V R; rw [expose_zero, Matrix.mulVec_zero]
  have HV: Green V:= (show ContDiffAt ℝ ω (fun u=>K *ᵥ u) (R 0) from by unfold R; rw [expose_zero]; exact board K).comp 0 (expose_green ..)
  change train (spool U) p=train (spool V) p
  apply mul_left_cancel₀ (a:=(PowerSeries.X: Ink (Active G B ⊕ Woods G c)) ^ 2) (pow_ne_zero _ X_ne_zero)
  conv_lhs=> arg 1; arg 1; rw [← train_X (spool U)]
  conv_rhs=> arg 1; arg 1; rw [← train_X (spool V)]
  rw [← map_pow,← map_pow,← map_mul,← map_mul,hz,traveling U (board _) (Matrix.mulVec_zero ..) k (penSmooth G S h), traveling V HV hV _ (penSmooth G S h)]; exact jet_congr hs

lemma bill_exact (P:PChart G f)(h:rollTest (flash P) (flash P) 1 0) (p:S.patch.Branches S.kernel G):
    let q:=reroll (path (U:=Woods G c)) (spool (internal S e (extractV G S B Q) (extractV G S T Q)))
    unscaled S B Q P=q (loom ℓ (unscaled S T Q P)):= by
  intro q
  rw [unscaled,unscaled,map_add,map_add]; exact congr_arg₂ (· + ·) (pan_price S e _ _ _ (primalSweeps S Q) (primalSweeps S Q) h) (pan_angular S e _ _ (primalSweeps S Q) (primalSweeps S Q) p)
end YM.WilsonCoeffUV.Power.Freedom
