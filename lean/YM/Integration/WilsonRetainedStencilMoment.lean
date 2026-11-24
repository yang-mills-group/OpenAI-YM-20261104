import YM.Integration.WilsonCoherentMayerProjection

/-! A regulator-uniform moment of the actual marked projection. The paid
resolvent of the original coat controls every submitted scalar variance.
Only the cardinality of the fixed Wilson stencil enters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedStencilMoment
open Function Filter Lattice RG Pressure Tree Wilson Source ConnectedActivityE6
open Coat Census Control Window RGLocalTaylor PhysicalNext.Repeat.Legato
open Finset MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)
open WilsonCoherentMayerProjection

abbrev Keys := Σ i:I, UsedEdges (R.family.localSection (d i)).stencil × G.ColorIndex

def restore : (Keys R d → ℝ) →L[ℝ] Panels R d :=
  ({toFun:=fun z i e=>WithLp.toLp 2 (fun j=>z ⟨i,e,j⟩)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl} : (Keys R d→ℝ) →ₗ[ℝ] Panels R d).toContinuousLinearMap

variable {c f L:Side} {S:StepData c f} (F:Forest S.ratio) (o:I→Site f)

def address (k:Keys R d) : Tubular f G := ((wrap f k.2.1.val.1+o k.1,k.2.1.val.2),k.2.2)

def sampled (z:Air f G) (k:Keys R d):ℝ :=
  if (address R d o k).1 ∈ F.trunks then 0 else z (address R d o k)

theorem original (z:Air f G): restrict R d F o z=restore R d (sampled R d F o z):=by
  funext i e
  ext j
  let b:Bond f:=(wrap f e.val.1+o i,e.val.2)
  change (if b∈F.trunks then (0:G.Color) else erect G (WithLp.ofLp z) b) j=
    if b∈F.trunks then 0 else z (b,j)
  split <;> rfl

private theorem power_sum {K:Type} [Fintype K] (a:K→ℝ) (p:ℕ):
    ‖a‖^(p+1)≤∑k,‖a k‖^(p+1):=by
  by_cases h:Nonempty K
  · letI:=h
    obtain ⟨i,_,hi⟩:=exists_max_image univ (fun k=>‖a k‖) univ_nonempty
    have cap:‖a‖≤‖a i‖:=(pi_norm_le_iff_of_nonneg (norm_nonneg (a i))).mpr (fun k=>hi k (mem_univ k))
    exact (pow_le_pow_left₀ (norm_nonneg _) cap _).trans (single_le_sum (fun k _=>pow_nonneg (norm_nonneg (a k)) _) (mem_univ i))
  · haveI:IsEmpty K:=not_nonempty_iff.mp h
    have hz:a=0:=Subsingleton.elim _ _
    simp [hz]

theorem point (p:ℕ) (z:Air f G):‖restrict R d F o z‖^(p+1)≤
    ‖restore R d‖^(p+1)*∑k:Keys R d,‖z (address R d o k)‖^(p+1):=by
  rw [original]
  apply (pow_le_pow_left₀ (norm_nonneg _) ((restore R d).le_opNorm _) _).trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
  apply (power_sum _ _).trans
  apply sum_le_sum
  intro k _
  by_cases h:(address R d o k).1∈F.trunks <;> simp [sampled,h]

variable {T:Tube G S} {P:Teller G} {η r Q Y:ℝ} {X:Coat T F}

theorem variance (h:Rotator P L η r Q Y X) (k:Tubular f G):
    X.relating k k ≤ payE η r Q (tubularPrice G L) :=by
  have bill:|X.relating k k|≤payE η r Q (tubularPrice G L):=by
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite,ite_mul,Coat.relating] using
      (Control.top (h.scale.mate X.shutter) h.scale.weather.1.le (Pi.single k (1:ℝ)))
  exact (le_abs_self _).trans bill

def unitMoment (n:ℕ):ℝ:=∫ t:ℝ,‖t‖^n ∂gaussianReal 0 1
private theorem unit_nonneg (n:ℕ):0≤unitMoment n := integral_nonneg (fun _=>by positivity)

theorem coordinate (h:X.relating.PosDef) (k:Tubular f G) (n:ℕ):
    (∫ z:Air f G,‖z k‖^n ∂X.dice)=(Real.sqrt (X.relating k k))^n*unitMoment n:=by
  let y:=fun z:Air f G=>z k
  let f':=fun t:ℝ=>‖t‖^n
  have my:Measurable y:=by fun_prop
  have mf:Measurable f':=by fun_prop
  have diag:0≤X.relating k k:=by simpa using h.posSemidef.dotProduct_mulVec_nonneg (Pi.single k (1:ℝ))
  have eq:(X.dice).map y=gaussianReal 0 (X.relating k k).toNNReal :=
    (measurePreserving_eval_multivariateGaussian (μ:=0) (i:=k) h.posSemidef).map_eq
  let std:=fun t:ℝ=>Real.sqrt (X.relating k k)*t
  have ht:Measurable std:=measurable_const.mul measurable_id
  have moved:(gaussianReal 0 1).map std=gaussianReal 0 (X.relating k k).toNNReal:=by
    rw [show std=(fun t:ℝ=>Real.sqrt (X.relating k k)*t) from rfl,gaussianReal_map_const_mul,mul_zero,mul_one]
    congr 1
    ext
    simp [Real.sq_sqrt diag,diag]
  change (∫ z:Air f G,f' (y z) ∂X.dice)=_
  rw [←integral_map my.aemeasurable mf.aestronglyMeasurable,eq,←moved,integral_map ht.aemeasurable mf.aestronglyMeasurable]
  simp [f',std,mul_pow,abs_of_nonneg (Real.sqrt_nonneg _),integral_const_mul,unitMoment]

/-- The price depends only on the enrolled stencil and the common physical
resolvent constants. Repeated positions and trunk deletions cost no extra. -/
theorem purchased (h:Rotator P L η r Q Y X) (p:ℕ):
    (∫z:Air f G,‖restrict R d F o z‖^(p+1) ∂X.dice)≤
    ‖restore R d‖^(p+1)*((Fintype.card (Keys R d):ℝ)*
       ((Real.sqrt (payE η r Q (tubularPrice G L)))^(p+1)*unitMoment (p+1))) :=by
  let A:=restrict R d F o
  haveI:IsGaussian X.dice:=inferInstanceAs (IsGaussian (multivariateGaussian 0 X.relating))
  have orig:Integrable (fun z:Air f G=>‖A z‖^(p+1)) X.dice:=by
    have hn:Integrable (fun u:Panels R d=>‖u‖^(p+1)) (X.dice.map A):=
      MemLp.integrable_norm_pow' (p:=p+1) (f:=id) (IsGaussian.memLp_id (X.dice.map A) _ (by simp))
    exact (integrable_map_measure (by fun_prop) A.continuous.aemeasurable).mp hn
  have each (k:Keys R d):Integrable (fun z:Air f G=>‖z (address R d o k)‖^(p+1)) X.dice:=by
    let L':Air f G→L[ℝ]ℝ:=EuclideanSpace.proj (address R d o k)
    have hn:Integrable (fun u:ℝ=>‖u‖^(p+1)) (X.dice.map L'):=
      MemLp.integrable_norm_pow' (p:=p+1) (f:=id) (IsGaussian.memLp_id (X.dice.map L') _ (by simp))
    exact (integrable_map_measure (by fun_prop) L'.continuous.aemeasurable).mp hn
  calc
    _ ≤ ∫z:Air f G,‖restore R d‖^(p+1)*(∑k:Keys R d,‖z (address R d o k)‖^(p+1)) ∂X.dice :=
      integral_mono orig ((integrable_finsetSum _ (fun k _=>each k)).const_mul _) (point R d F o p)
    _ = ‖restore R d‖^(p+1)*∑k:Keys R d, (∫z:Air f G,‖z (address R d o k)‖^(p+1) ∂X.dice):=by
      rw [integral_const_mul,integral_finsetSum _ (fun k _=>each k)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
      let fee:=Real.sqrt (payE η r Q (tubularPrice G L))^(p+1)*unitMoment (p+1)
      calc
        _ ≤ ∑ _k:Keys R d,fee := by
          apply sum_le_sum
          intro k _
          rw [coordinate F h.fullC]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _)
            (Real.sqrt_le_sqrt (variance F h _)) _) (unit_nonneg _)
        _ = _ := by simp [fee]

end YM.Integration.WilsonRetainedStencilMoment
