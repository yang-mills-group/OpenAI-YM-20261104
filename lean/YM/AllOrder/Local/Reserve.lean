import YM.AllOrder.Local.Rounding
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogosG

/-!
# Full Gaussian volumes and young tail for arbitrary order.

To uncut each of the canonical stationary moments; no reduction of dimension
or independent-tag trick. Prices uniform on the auxiliary volumes (≤ stated
post-L horizon D, not actual arbitrary polymer boxes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Vote
open Function Filter Set Finset Matrix Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Gauge Input Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush PhysicalNext Repeat Lantern Poll
open scoped Topology Classical ContDiff ENNReal

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {j k : ℕ} {p c u v D C : ℝ} {M : Matrix ι ι ℝ}
    (h : M.PosDef) (he : ∀ z:ι → ℝ, dotProduct z (M *ᵥ z) ≤ c*dotProduct z z)

def volumeCost (c : ℝ) (j : ℕ) (P : ℝ) := (1+P)^j*(1+P*(2*Real.exp (c*(j:ℝ)^2/2)))
lemma vn {p:ℝ} (hh : 0≤p) : 0 ≤ volumeCost c j p := by unfold volumeCost; positivity
lemma vc {p q c:ℝ} {j:ℕ} (hp : 0≤p) (hh : p ≤ q) : volumeCost c j p ≤ volumeCost c j q := by
  have hx:=hp.trans hh; unfold volumeCost; gcongr
lemma v_rate {G : Gauge} {L : Side} {f : ℝ → ℝ} (hp : Rate G L 0 f) (c:ℝ) (j:ℕ) :
    Rate G L 0 (fun t=> volumeCost c j (f t)) :=
  Brim.bell (Brim.prep ((Rate.const 1).add hp) j) ((Rate.const 1).add (hp.mul_right _))

include h he
lemma radial (j:ℕ) (hh : (Fintype.card ι:ℝ) ≤ p) :
    let g (z:Body ι) := (1+‖z‖)^j
    Integrable g (sweep M) ∧ ∫ z, g z ∂(sweep M) ≤ volumeCost c j p := by
  let k:ℝ:= Fintype.card ι; have hp':0 ≤ k:= by unfold k; positivity
  let s:=2*Real.exp (c*(j:ℝ)^2/2)
  intro g
  have ha i: |M i i| ≤ c:= by
    have hM : 0 ≤ M i i:= h.posSemidef.diag_nonneg
    have hh := he (Pi.single i 1)
    rw [abs_of_nonneg hM]; simpa [Matrix.mulVec_single] using hh
  let f (x:Body ι):= ∑ i, (1+|x i|)^j; obtain ⟨hF,hg⟩:= Flux.salience univ h.posSemidef ha j; rw [Finset.card_univ] at hg
  have hx (x:Body ι) : g x ≤ (1+k)^j*(1+f x) := by
    cases isEmpty_or_nonempty ι
    · simp [k,f,g, Subsingleton.elim x (0:Body ι)]
    obtain ⟨i,-,he⟩:= Finset.exists_max_image univ (fun i:ι=>|x i|) Finset.univ_nonempty
    have hi : ‖x‖ ≤ (1+k)*|x i|:= by
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (1+k)*|x i|), EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _ : ι, |x i|^2:= Finset.sum_le_sum fun j hj=> by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (he j hj) 2
        _ = k* |x i|^2:= by simp [k]
        _ ≤ _ := by rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
    apply le_trans (b:= ((1+k)*(1+|x i|))^j)
    · apply pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x‖); linarith
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((Finset.single_le_sum (f:=fun t=> (1+|x t|)^j) (fun t _=> by positivity) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
  have hs:Integrable (fun x:Body ι => 1+f x) (sweep M):= (integrable_const 1).add hF
  have hz := hs.const_mul ((1+k)^j)
  have hG : Integrable g (sweep M):= hz.mono' (by unfold g; fun_prop) (ae_of_all _ fun x=> (Real.norm_of_nonneg (show 0 ≤ g x by unfold g; positivity)).trans_le (hx x))
  refine ⟨hG,(integral_mono hG hz hx).trans ((le_trans ?_ (vc hp' hh)))⟩
  unfold volumeCost; rw [integral_const_mul, integral_add (integrable_const _) hF, integral_const, probReal_univ,one_smul]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hg) (by positivity)

variable {f : Body ι → Y} (hg : AEStronglyMeasurable f (sweep M))
    (hh : (Fintype.card ι : ℝ) ≤ p) (hp : ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^j)
include hh hp
omit h he [NormedSpace ℝ Y] [CompleteSpace Y] [DecidableEq ι] hh in
lemma nz : 0 ≤ C := by
  have he := (norm_nonneg (f (0:Body ι))).trans (hp 0); simp only [norm_zero,add_zero,one_pow,mul_one] at he; exact he
include hg
omit [CompleteSpace Y] in
lemma average [CompleteSpace Y]  : Integrable f (sweep M) ∧ ‖∫ x,f x ∂(sweep M)‖ ≤ C * volumeCost c j p := by
  obtain ⟨hm,hv⟩:= radial h he j hh
  have hg':= hm.const_mul C; have hx:Integrable f (sweep M) := hg'.mono' hg (ae_of_all _ fun x=> hp x)
  refine ⟨hx,(norm_integral_le_integral_norm _).trans ((integral_mono hx.norm hg' hp).trans ?_)⟩
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hv (nz hp)

/-- `t` chosen **large** to debit exponentially-small tail measure. -/
lemma lift_tail (D t:ℝ) (ht:0<t) :
    let Z := (closedBall (0:Body ι) D)ᶜ
    ‖∫ x, Z.indicator f x ∂(sweep M)‖ ≤ C*(t*(sweep M).real Z+ (volumeCost c (2*j) p)/t) := by
  intro Z; let μ:=sweep M
  have hZ: MeasurableSet Z:=measurableSet_closedBall.compl; let g (z:Body ι):=(1+‖z‖)^j; let k (z:Body ι):=(1+‖z‖)^(2*j)
  have hC:= nz hp
  have hExp : ∀ a:ℝ,a ≤ t+a^2/t := by
    intro a; rw [← sub_le_iff_le_add',le_div_iff₀ ht]; nlinarith [sq_nonneg (a-t/2)] -- orientation
  obtain ⟨hK,hv⟩:= radial h he (2*j) hh; have hl:= hK.div_const t; let V:= Z.indicator (fun _=>t); have hV:= (integrable_const (μ:=μ) t).indicator hZ
  have hx: ∀ x, ‖Z.indicator f x‖ ≤ C*(V x+k x/t):= by
    intro x
    by_cases H:x∈Z
    · have he': k x=(g x)^2:= by unfold k g; rw [mul_comm 2,pow_mul]
      unfold V; rw [indicator_of_mem H, indicator_of_mem H, he']; exact (hp x).trans (mul_le_mul_of_nonneg_left (hExp _) hC)
    unfold V; rw [indicator_of_notMem H,indicator_of_notMem H,norm_zero]; unfold k; positivity
  have h' := (norm_integral_le_integral_norm _).trans (integral_mono ((average h he hg hh hp).1.indicator hZ|>.norm) ((hV.add hl|>.const_mul C) : Integrable (fun x=> C*(V x+k x/t)) μ) hx)
  refine h'.trans ?_; simp only [Pi.add_apply]; rw [integral_const_mul,integral_add hV hl,integral_indicator hZ, integral_div, setIntegral_const]; exact mul_le_mul_of_nonneg_left (add_le_add (by rw [smul_eq_mul, mul_comm]) (div_le_div_of_nonneg_right hv ht.le)) hC
end YM.AllOrder.Local.Vote
