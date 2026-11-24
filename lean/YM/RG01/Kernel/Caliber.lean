import YM.Extra.SOURCE_HISTORIES.Offsets
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
/-!
# Probability scale of the literal conditional fine denominator

Normalize once, on the actual step. Use relative estimates throughout,
so no cost proportional to the vacuum scalar or exponential in torus
volume enters ANY license (volume-dependent compactness OK only in
proving qualititative integrability/measurability). The functions on which
one can directly get this particular sub-estimate are supply tilts of the
actual conditional law, bounded with respect to its whole support (source tags
may depend on physical fine configuration). This is not estimating an
already re-rendered coarse RG residue by the sup of its evaluated density or
silently presuming integrability of off-mask germs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset
open Lattice Wilson RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {κ Ω:Type} [Fintype κ] [MeasurableSpace Ω] {μ:Measure Ω}

/-- Weights after conditioning, with respect to probability Haar over fine config
and *counting* measure over kernel choices (all probability masses already in density). -/
structure Caliber (w : κ → Ω → ℝ) (μ: Measure Ω): Prop where
    fund (i) : Integrable (w i) μ
    pos (i U): 0≤w i U
    revenue : ∑ i, (∫ x,w i x ∂μ)=1
variable {w:κ→Ω→ℝ}
def moment (w:κ→Ω→ℝ) (μ:Measure Ω) (F:κ→Ω→ℂ) := ∑ i, (∫ x, (w i x:ℂ)*F i x∂μ)
abbrev Bounded (μ:Measure Ω)(F:κ→Ω→ℂ)(M:ℝ) := (∀ i, AEStronglyMeasurable (F i) μ) ∧ ∀ i x, ‖F i x‖≤M
namespace Caliber
variable (H:Caliber w μ)
include H
variable {F:κ→Ω→ℂ}{M:ℝ}
lemma funds (ht:Bounded μ F M)(i:κ): Integrable (fun x=> (w i x:ℂ)*F i x) μ := by
  have he:= (H.fund i).ofReal (𝕜:=ℂ)
  refine (he.mul_const (M:ℂ)).norm.mono' (he.1.mul (ht.1 i)) (ae_of_all _ fun x=> ?_)
  have hx:0 ≤ M:= (norm_nonneg _).trans (ht.2 i x)
  change ‖(w i x:ℂ) * F i x‖ ≤ ‖(w i x:ℂ) * (M:ℂ)‖
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hx,Real.norm_of_nonneg (H.pos _ _)]; exact mul_le_mul_of_nonneg_left (ht.2 i x) (H.pos _ _)
lemma price (hF: Bounded μ F M): ‖moment w μ F‖ ≤ M := by
  unfold Kernel.moment
  apply le_trans (norm_sum_le ..)
  rw [show M=(∑ i, (∫ x, w i x∂μ))*M by rw [H.revenue,one_mul],sum_mul]
  refine Finset.sum_le_sum fun i _=> (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  refine integral_mono ((H.funds hF i).norm) ((H.fund i).mul_const _) ?_
  intro x; dsimp only; rw [norm_mul,norm_real, Real.norm_eq_abs,abs_of_nonneg (H.pos _ _)]; exact mul_le_mul_of_nonneg_left (hF.2 i x) (H.pos _ _) -- fix
lemma unit : moment w μ 1=1 := by
  unfold moment; simp_rw [Pi.one_apply,mul_one]; have he (i:κ):(∫ x,(w i x:ℂ)∂μ) = ↑(∫ x,w i x∂μ) := integral_ofReal (𝕜:=ℂ); simp_rw [he,←Complex.ofReal_sum,H.revenue]; rfl
lemma decrease (C:κ→Ω→ℂ)(h:Bounded μ (F-C) M){m : ℝ}(hC:Bounded μ C m) :
    ‖moment w μ F-moment w μ C‖ ≤ M := by
  convert! H.price h using 1
  unfold moment; rw [← Finset.sum_sub_distrib]; apply congr_arg; apply Finset.sum_congr rfl; intro i hi
  have hs:F=(F-C)+C:= Eq.symm (sub_add_cancel _ _)
  have he:Bounded μ F (M+m):=by
    apply And.intro (hs ▸ (show ∀ i,AEStronglyMeasurable (((F-C)+C) i) μ from fun i=>(h.1 i).add (hC.1 i))) -- replace rw
    intro i x; rw [show F i x=(F-C) i x+C i x by simp]
    exact (norm_add_le ..).trans (add_le_add (h.2 i x) (hC.2 i x))
  rw [← integral_sub (H.funds he i) (H.funds hC i)]; simp_rw [Pi.sub_apply,mul_sub]
end Caliber

section step
variable {G : Gauge}{N n m:ℕ} (H:History G)(h:H.Selected)(V:Config G (H.S.side m n))
local notation "S"=> H.levels.clock.op m n
abbrev upper (N n m : ℕ) := H.rep N n (m+1)
def expense (N m n:ℕ)(V:Config G (H.S.side m n))(i:(H.levels.clock.op m n).Choices)(U : Config G (H.S.side (m+1) n)) := let R:=upper H N n m
    (H.levels.clock.op m n).likelihood U i*(H.levels.clock.op m n).noise R.beta ((H.levels.clock.op m n).prediction U i) V*R.eval U/(H.rep N n m).eval V
variable (N)(hm:m<N)
include h hm
set_option maxHeartbeats 150000 in
lemma actual : Caliber (expense H N m n V) (Wilson.prior G (H.S.side (m+1) n)):=by
  let s:= S; let μ:= Wilson.prior G (H.S.side (m+1) n); let R:= upper H N n m; let D:=(H.rep N n m).eval V; let F:= Config G (H.S.side (m+1) n)
  have he U := Extra.Histories.Tour.bright H h N n (m+1) hm U
  have hd : 0<D:=Extra.Histories.Tour.bright H h N n m hm.le V
  have hh:= (H.levels.blocks m n).branches
  have hE:Integrable R.eval μ:= (R.envelope (h.represents _ _ _ hm).good).integrable _
  let u (i:s.Choices)(U:F) := s.likelihood U i*s.noise R.beta (s.prediction U i) V
  have hp (i:s.Choices)(U:F) : 0≤ u i U:= mul_nonneg (s.likelihood_pos ..) (prod_nonneg fun j _=> mul_nonneg (inv_nonneg.mpr (s.penaltyZ_pos _).le) (Real.exp_pos _).le)
  have ht (i:s.Choices): Measurable (u i) := by
    unfold u
    have he : Measurable (fun t:F=> (s.prediction t i, V)):= (s.prediction_meas hh i).prodMk measurable_const
    have hf:= Measurable.comp (s.noise_cont (G:=G) R.beta|>.measurable) he
    exact (s.likelihood_meas hh i).mul hf
  obtain ⟨C,hC⟩:= s.density_bound hh R.beta
  have hK (i:s.Choices)(U:F) : ‖u i U‖ ≤ C:= by
    rw [Real.norm_eq_abs,abs_of_nonneg (hp _ _)]; apply le_trans (Finset.single_le_sum (f:=fun i=>u i U) (fun _ _=> hp _ _) (mem_univ _)) (hC U V)
  have hf i: Integrable (fun U=> u i U*R.eval U) μ:=hE.bdd_smul C (ht i).aestronglyMeasurable (ae_of_all _ (hK i))
  refine ⟨fun i=> (hf i).div_const D,fun i U=> div_nonneg (mul_nonneg (hp i U) (he U).le) hd.le, ?_⟩
  have hx:=congr_fun (h.steps N n m hm|>.1) V
  change D=(∫ U:F, (∑ i:s.Choices,u i U)*R.eval U∂μ) at hx
  change ∑ i:s.Choices,(∫ U:F,u i U*R.eval U/D∂μ)=_
  conv_lhs => enter [2, i]; rw [integral_div]
  rw [← sum_div]
  apply (div_eq_one_iff_eq hd.ne').mpr; rw [hx, ← integral_finsetSum univ (fun i _=>hf i)]; simp only [Finset.sum_mul]
end step
end YM.RG01.Kernel
