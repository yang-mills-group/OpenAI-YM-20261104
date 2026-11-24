import YM.Integration.WilsonPhysicalHistoryRetainedSpringVisits
import YM.Integration.WilsonRetainedStencilMoment

/-! Every ordered bond on a previously deposited curvature row is sampled
by the same original Gaussian, with the actual funded covariance. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MeasureTheory ProbabilityTheory Matrix WilsonMeasuredPathTaylor WilsonRetainedStencilMoment
open scoped BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

def colorReader (G : Gauge) : (G.ColorIndex→ℝ)→L[ℝ]G.Color :=
  ({toFun:=fun z=>WithLp.toLp 2 z
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl} : (G.ColorIndex→ℝ)→ₗ[ℝ]G.Color).toContinuousLinearMap

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {η r Q Y : ℝ} {X : Coat T F}

def scalarPrice (G : Gauge) (L : Side) (η r Q : ℝ) (q : ℕ) : ℝ :=
  (1+Real.sqrt (payE η r Q (tubularPrice G L)))*(1+unitMoment (q+1))

def speedPrice (G : Gauge) (L : Side) (η r Q : ℝ) (q : ℕ) : ℝ :=
  (1+G.colorScale*‖colorReader G‖)*(1+(Fintype.card G.ColorIndex:ℝ))*scalarPrice G L η r Q q

theorem scalar_price (h : Rotator P L η r Q Y X) (q : ℕ) (l : Tubular f G) :
    Integrable (fun z : Air f G=>‖z l‖^(q+1)) X.dice ∧
    (∫ z : Air f G,‖z l‖^(q+1) ∂X.dice)≤(scalarPrice G L η r Q q)^(q+1) := by
  haveI : IsGaussian X.dice:=inferInstanceAs (IsGaussian (multivariateGaussian 0 X.relating))
  let A : Air f G→L[ℝ]ℝ:=EuclideanSpace.proj l
  have hn : Integrable (fun u : ℝ=>‖u‖^(q+1)) (X.dice.map A):=
    MemLp.integrable_norm_pow' (p:=q+1) (f:=id) (IsGaussian.memLp_id (X.dice.map A) _ (by simp))
  refine ⟨(integrable_map_measure (by fun_prop) A.continuous.aemeasurable).mp hn,?_⟩
  have unit0 : 0≤unitMoment (q+1):=integral_nonneg fun z : ℝ=>by positivity
  rw [coordinate F h.fullC]
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
    (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (variance F h l)) _) unit0)
  rw [scalarPrice,mul_pow]
  exact mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_add_of_nonneg_left zero_le_one) _)
    ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (by linarith : 1≤1+unitMoment (q+1)) (by omega)))
    unit0 (by positivity)

theorem speed_price_pos (G : Gauge) (L : Side) (η r Q : ℝ) (q : ℕ) : 0 < speedPrice G L η r Q q := by
  have unit0 : 0≤unitMoment (q+1):=integral_nonneg fun z : ℝ=>by positivity
  have scale0:=G.colorScale_pos
  unfold speedPrice scalarPrice
  positivity

theorem field_speed (h : Rotator P L η r Q Y X) (q : ℕ) (e : Edge (Site f)) :
    AEStronglyMeasurable (fun z=>speed (WilsonCoherentMayerNoise.row F z) e) X.dice ∧
    Integrable (fun z=>speed (WilsonCoherentMayerNoise.row F z) e^(q+1)) X.dice ∧
    (∫ z,speed (WilsonCoherentMayerNoise.row F z) e^(q+1) ∂X.dice)≤(speedPrice G L η r Q q)^(q+1) := by
  by_cases he : e∈F.trunks
  · have zero (z : Air f G) : speed (WilsonCoherentMayerNoise.row F z) e=0:=by
      simp [speed,WilsonCoherentMayerNoise.row,he]
    simp_rw [zero,zero_pow (Nat.succ_ne_zero q)]
    exact ⟨aestronglyMeasurable_const,integrable_zero (Air f G) ℝ X.dice,(integral_zero ..).le.trans
      (pow_nonneg (speed_price_pos G L η r Q q).le _)⟩
  let w (z : Air f G) (b : G.ColorIndex):=z (e,b)
  let A:=scalarPrice G L η r Q q
  have unit0 : 0≤unitMoment (q+1):=integral_nonneg fun z : ℝ=>by positivity
  have pos : 0<A:=by dsimp only [A,scalarPrice]; positivity
  have pool:=QLocalMeasuredPathMoments.pooled X.dice univ (fun _ : G.ColorIndex=>A)
    (fun b z=>‖w z b‖) (fun _ _=>pos) (fun _ _ _=>norm_nonneg _)
    (fun b _=>(show Continuous (fun z=>w z b) from (EuclideanSpace.proj (𝕜:=ℝ) (e,b)).continuous).norm.aestronglyMeasurable)
    q (fun b _=>scalar_price h q (e,b))
  have eq (z : Air f G) : speed (WilsonCoherentMayerNoise.row F z) e=G.colorScale*‖colorReader G (w z)‖ := by
    simp only [speed,WilsonCoherentMayerNoise.row,if_neg he,G.colorMat_norm]
    rfl
  have cont : Continuous w:=continuous_pi fun b=>(EuclideanSpace.proj (𝕜:=ℝ) (e,b)).continuous
  have measurable : AEStronglyMeasurable (fun z=>speed (WilsonCoherentMayerNoise.row F z) e) X.dice := by
    simp_rw [eq]
    exact (continuous_const.mul ((colorReader G).continuous.comp cont).norm).aestronglyMeasurable
  have bound (z : Air f G) : speed (WilsonCoherentMayerNoise.row F z) e≤(G.colorScale*‖colorReader G‖)*∑ b,‖w z b‖ := by
    rw [eq,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ G.colorScale_pos.le
    apply ((colorReader G).le_opNorm _).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    exact (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _=>norm_nonneg _)).mpr fun b=>
      single_le_sum (fun i _=>norm_nonneg (w z i)) (mem_univ b)
  have raised (z : Air f G) : speed (WilsonCoherentMayerNoise.row F z) e^(q+1)≤
      (G.colorScale*‖colorReader G‖)^(q+1)*(∑ b,‖w z b‖)^(q+1) := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (bound z) _
  have scale0:=G.colorScale_pos
  have rhs:=pool.1.const_mul ((G.colorScale*‖colorReader G‖)^(q+1))
  have actual:=rhs.mono' (measurable.pow (q+1)) (ae_of_all _ fun z=>
    (Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)).le.trans (raised z))
  refine ⟨measurable,actual,(integral_mono actual rhs raised).trans ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left pool.2 (by positivity)).trans
  rw [←mul_pow,Finset.sum_const,card_univ,nsmul_eq_mul]
  apply pow_le_pow_left₀ (by positivity)
  unfold speedPrice
  dsimp only [A]
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)) pos.le

end YM.Integration.OriginalMarkedRunAction
