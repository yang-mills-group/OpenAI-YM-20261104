import YM.RG01Estimate.ConditionalBasic
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens
/-!
# Real smooth Taylor algebra, with uniform derivative budgets in unscaled variables

We use the FTC coefficients (resolution by one factor `b`, repeated). In particular
use for negative prefactors: the resolved function uses actual n-jets, even at zero where
multiplying by b⁻ⁿ would not work. Cumulants can use `peano/prices` to identify these
with the b Taylor coefficients in any equivalent algebra (orders quantified). No price
depends on dimension here. No complex inverse or entire assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.RealTaylor
open Function Filter Set Metric Finset MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Brush
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "X" => ℝ × E
local notation "T" => (Set.Icc (0:ℝ) 1)
variable (f : ℝ × E → F) {C p d : ℝ} {k j : ℕ}

def lerp (t:ℝ) (x:X) := (t*x.1,x.2)
def tjet (t:ℝ) (x:X) := fderiv ℝ f (lerp t x) (1,0)
def drop (x:X) := ∫ t:ℝ in 0..1, tjet f t x

def corridor (d:ℝ) (s:Set E) := ball (0:ℝ) d ×ˢ s
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma inner_jet (s : Set E) (x:X) (hx : x∈ corridor d s) (t:ℝ)(ht:t∈T) :
      lerp t x ∈ corridor d s := by
  refine ⟨?_,hx.2⟩
  rw [mem_ball_zero_iff]; unfold lerp; simp only [norm_mul]; rw [Real.norm_of_nonneg ht.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) (mem_ball_zero_iff.mp hx.1)

lemma linear_compression {H Q : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : Q→ H} {x : Q} (L:H→L[ℝ] F)(h : Brush k C d f x) (ht : ‖L‖ ≤ p) :
    Brush k (p*C) d (L ∘ f) x := by
  refine ⟨L.contDiff.contDiffAt.comp x h.smooth,h.pos,fun i hi=>?_⟩
  unfold normJ; rw [L.iteratedFDeriv_comp_left h.smooth (by exact_mod_cast hi)]
  exact L.norm_compContinuousMultilinearMap_le _ |>.trans ((mul_le_mul ht (h.order _ hi) (norm_nonneg _) ((norm_nonneg _).trans ht)).trans_eq (mul_assoc ..).symm)

lemma term (t:ℝ) (ht:t∈T) (x:X) (hp : Brush (j+1) C 1 f (lerp t x)) :
    Brush j C 1 (tjet f t) x := by
  let L:X →L[ℝ] X:= ContinuousLinearMap.prod (t • ContinuousLinearMap.fst ℝ ℝ E) (ContinuousLinearMap.snd ℝ ℝ E)
  let K:= ContinuousLinearMap.apply ℝ F ((1:ℝ),(0:E))
  have hk : ‖K‖≤ 1:= (Lantern.beam_at ..).trans (by simp)
  have hf : L x= lerp t x:= rfl
  have hL:‖L‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=>by
     rw [one_mul]; apply max_le _ (norm_snd_le y); change ‖t*y.1‖ ≤ ‖y‖; rw [norm_mul,Real.norm_of_nonneg ht.1]
     exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_fst_le y))
  have h : Brush j C (1*1) (fun i=> fderiv ℝ f (L i)) x:= Brush.reading L (show Brush j C 1 (fderiv ℝ f) (L x) from norm_F hp) hL
  have h:= linear_compression K h hk; rw [one_mul,one_mul] at h; exact h
lemma connected (x:X) (h:∀ t∈ T, Brush (j+1) C 1 f (lerp t x)) : ContinuousOn (fun t=> tjet f t x) T := by
  have hb:Continuous (fun t:ℝ=> lerp t x) := by unfold lerp; fun_prop
  intro t ht; apply ContinuousAt.continuousWithinAt
  exact ((ContinuousLinearMap.apply ℝ F ((1:ℝ),(0:E))).continuous.continuousAt).comp (((norm_F (h t ht)).smooth.continuousAt).comp (f:=fun t=>lerp t x) hb.continuousAt)
lemma layer [CompleteSpace F] (x:X) (h:∀ t∈ T, Brush (j+1) C 1 f (lerp t x)) :
     f x= f ((0:ℝ),x.2)+ x.1 • RealTaylor.drop f x := by
  have he t (ht:t∈T) : HasDerivAt (fun v:ℝ=> f (lerp v x)) (x.1 • tjet f t x) t:= by
     have hg:HasDerivAt (fun v:ℝ=> lerp v x) (x.1 • ((1:ℝ),(0:E))) t:=by
        refine HasDerivAt.congr_deriv (HasDerivAt.prodMk ((hasDerivAt_id' t).mul_const (x.1)) (hasDerivAt_const _ x.2)) ?_
        simp
     have h' := (((h t ht).smooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hg)
     rw [map_smul] at h'; exact h'
  have hb : IntervalIntegrable (fun t:ℝ=> x.1 • tjet f t x) volume 0 1:= ((connected f x h).const_smul _).intervalIntegrable_of_Icc zero_le_one
  have hl := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (uIcc_of_le (α:=ℝ) zero_le_one|>.symm ▸ he) hb
  rw [intervalIntegral.integral_smul, show lerp 1 x=x from by simp [lerp], show lerp 0 x= (0,x.2) from by simp [lerp] ] at hl
  unfold RealTaylor.drop; rw [hl]; abel

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable (Z : Set E) (u : ℝ) (hp : IsOpen Z)
local notation "Y" => corridor u Z
-- all output applications are scalar/finite dimensional; same comp cost.
include hp
lemma pay_down (x:X) (hx:x∈ Y)
    (h : ∀ x∈ Y, Brush (j+1) C 1 f x) : Brush j C 1 (RealTaylor.drop f) x := by
   let g(y:X) := (T).indicator (fun t=> tjet f t y)
   let μ:= volume (α:=ℝ) |>.restrict (Ioc 0 1)
   have hU y (hy:y∈ Y) : ContinuousOn (fun t=> tjet f t y) T:= connected f y (fun t ht=> h _ (inner_jet Z _ hy t ht))
   letI:IsFiniteMeasure μ := by unfold μ; infer_instance
   letI : MeasurableSpace F := borel _
   letI := BorelSpace.mk (α:=F) rfl
   have hs : Y∈𝓝 x:= IsOpen.mem_nhds (isOpen_ball.prod hp) hx
   have hF (y) (hy:y∈Y) : StronglyMeasurable (g y):=by
      apply Measurable.stronglyMeasurable
      apply measurable_of_restrict_of_restrict_compl (s:=T) measurableSet_Icc
      · rw [show (T).restrict (g y)= (Set.Icc 0 1).restrict (fun t=> tjet f t y) from funext fun i=> indicator_of_mem i.2 (fun x=> tjet f x y)]; exact (continuousOn_iff_continuous_restrict.mp (hU y hy)).measurable
      rw [show (Tᶜ).restrict (g y)=(fun _=> 0) from funext fun i=> indicator_of_notMem i.2 (fun x=> tjet f x y)]; exact measurable_const
   have hC : 0 ≤ C := (h x hx).nonneg
   have h' (y) (hy:y∈ Y) t : Brush j C 1 (fun x=> g x t) y:= by
     by_cases ht:t∈ T
     · exact (term f t ht y (h _ (inner_jet Z y hy t ht))).shimmy (Eventually.of_forall fun _=> indicator_of_mem ht _)
     exact (((Brush.certified zero_le_one (0:F)).climb (by simpa using hC) le_rfl).shimmy (Eventually.of_forall fun _=> indicator_of_notMem ht _))
   have hc:∀ᶠ y in 𝓝 x,y∈ Y := hs
   have hh := UVExt.EnergyRay.Thermal.Core.meristem_complex (f:=g) (μ:=μ) (hc.mono hF)
      ⟨fun _=> C,integrable_const _, hc.mono fun y hy=> h' y hy⟩
   have hu : μ.real Set.univ=1:= by unfold μ; simp [Measure.real]
   refine (hh.1.buds (fun _=> C) (integrable_const _) zero_le_one (by rw [integral_const,hu,one_smul]) (ae_of_all _ (h' x hx))).shimmy ?_
   filter_upwards with y; unfold RealTaylor.drop; rw [intervalIntegral.integral_of_le zero_le_one]
   apply integral_congr_ae; filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioc (0:ℝ) 1) measurableSet_Ioc] with z hz; exact Eq.symm (indicator_of_mem (Ioc_subset_Icc_self hz) _)
-- Peano remainder by dropping b factors freeing finite Taylor read

def pages (f : ℝ × E → F)(j:ℕ):ℝ×E→F := Nat.rec f (fun _ => RealTaylor.drop) j

def piece (j:ℕ)(y:E):= pages f j (0,y)
def trunc (n:ℕ)(b:ℝ)(y:E) := ∑ i∈ Finset.range n, b^i • piece f i y
lemma projected (x:X) (hx:x∈ Y) (n:ℕ) (h: ∀ y∈Y,Brush (j+n) C 1 f y) :
    Brush j C 1 (pages f n) x := by
  induction n generalizing j x with
  | zero=>exact h _ hx
  | succ i ih=>exact pay_down (pages f i) Z u hp x hx (fun y hy=> ih y hy (by rw [show j+1+i=j+(i+1) by omega]; exact h))
lemma priced (x:X)(hx:x∈Y)(n:ℕ)(h:∀ y∈Y,Brush (j+n) C 1 f y):
    f x = trunc f n x.1 x.2+x.1^n • pages f n x := by
  induction n with
  | zero=>simp [trunc,pages]
  | succ i ih=>
    have he:= ih (fun y hy => (h y hy).smaller (by omega))
    have hX y (hy:y∈Y) := projected f Z u hp y hy i (j:=j+1) (by rw [show j+1+i=j+(i+1) by omega]; exact h)
    have hv := layer (pages f i) x (j:=j) (fun t ht=> hX _ (inner_jet Z _ hx t ht))
    rw [he,hv,show trunc f (i+1) x.1 x.2= trunc f i x.1 x.2+x.1^i • piece f i x.2 from Finset.sum_range_succ .., smul_add, smul_smul, pow_succ]
    change _=_+(x.1^i*x.1) • RealTaylor.drop (pages f i) x
    unfold piece; rw [add_assoc]

lemma priced_piece (y:E)(hy:y∈ Z)(n:ℕ)(he:0<u) (h : ∀ x∈Y,Brush (j+n) C 1 f x) :
    Brush j C 1 (piece f n) y:= by
   let L:= ContinuousLinearMap.inr ℝ ℝ E
   have hx:= projected f Z u hp (L y) (show (0,y)∈ Y from ⟨mem_ball_self he,hy⟩) n h
   have hh:= Brush.reading L hx Lantern.n_hook; rw [one_mul] at hh; exact hh

lemma priced_defect (b : ℝ)(y:E)(hB: (b,y) ∈ Y)(n : ℕ)(h : ∀ x∈Y,Brush (j+n) C 1 f x) :
    Brush j (|b|^n*C) 1 (fun y=> f (b,y) - trunc f n b y) y:= by
  let L := ContinuousLinearMap.inr ℝ ℝ E; have ht x:(b,(0:E))+L x=(b,x):=by simp [L]
  have hd:= Lantern.skim (P:=L) y ((ht y) ▸ projected f Z u hp (b,y) hB n h) Lantern.n_hook
  have hv:= hd.smul (b^n); simp only [ht] at hv; rw [Real.norm_eq_abs,abs_pow] at hv; apply hv.shimmy
  filter_upwards [hp.mem_nhds hB.2] with z hz; rw [priced f Z u hp (b,z) (by exact ⟨hB.1,hz⟩) n h]; simp
-- buy an actual g⁻n prefactor through valuation.
lemma priced_pole (n : ℕ) (hv: ∀ y∈Z,∀ k<n, piece f k y=0) (h : ∀ x∈Y,Brush (j+n) C 1 f x) :
    ∀ x∈Y, f x=x.1^n • pages f n x := by
  intro x hx; rw [priced f Z u hp x hx n h]
  unfold trunc; rw [Finset.sum_eq_zero,zero_add]; intro i ih; rw [hv _ hx.2 _ (Finset.mem_range.mp ih),smul_zero]
end YM.RG01Estimate.RealTaylor
