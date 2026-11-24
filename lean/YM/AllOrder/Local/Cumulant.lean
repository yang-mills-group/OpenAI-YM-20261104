import YM.AllOrder.Local.Branch
import YM.AllOrder.Local.Moments

/-!
# Real stationary Taylor orders after conditional denominator

Coefficients computed solely from input actions/section jets then full Gaussian
moments; not an assumed comparison coefficient. This is a local definition,
finite(period); more work to identify prescription at other stages or in the
limit. Exact equality of all lower polynomial jets when increasing order.
Weight comparison consumes physical `Golf` and post-L charges below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Vote
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Gauge Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush PhysicalNext Repeat Lantern Poll Work.G05
open scoped Topology Classical ContDiff ENNReal

section taylor
open Taylor
variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f g : E → Y} {a : ℝ} {j k n:ℕ} {x:E}
def terms (n:ℕ) (M : ∀ k, Tensor.T E Y k) := ∑ j∈Finset.range (n+1),Tensor.diagonal (M j)
variable (M N : ∀ k, Tensor.T E Y k)

lemma terms_art : ContDiff ℝ ω (terms n M) := by rw [show terms n M=(fun x=>∑ i∈Finset.range (n+1),Tensor.diagonal (M i) x) from funext fun x=> Finset.sum_apply x _ _]; exact ContDiff.sum (s:=Finset.range (n+1)) (f:=fun i=> Tensor.diagonal (M i)) (fun i _=> Tensor.diag_smooth ..) -- eta apply?

lemma terms_step (h : k ≤ n) : iteratedFDeriv ℝ k (terms (n+1) M) 0= iteratedFDeriv ℝ k (terms n M) 0:= by
  rw [show terms (n+1) M=terms n M + Tensor.diagonal (M (n+1)) from Finset.sum_range_succ _ (n+1),iteratedFDeriv_add_apply ((terms_art M).contDiffAt.of_le le_top) (Tensor.diag_smooth ..|>.contDiffAt), Taylor.diag_flat (M (n+1)) k (by omega),add_zero]
lemma terms_le (h : k≤j) (hh : j≤n) :
    iteratedFDeriv ℝ k (terms j M) 0=iteratedFDeriv ℝ k (terms n M) 0 := by
  induction hh with
  | refl => rfl
  | step hl ih => exact ih.trans (terms_step M (h.trans hl)).symm

lemma term_brush (x:E) (n:ℕ) {a:ℝ} (h: ∀ k≤n,(k.factorial:ℝ)* ‖M k-N k‖ ≤ a) (hx:‖x‖≤1) (j:ℕ) :
     Brush j ((n+1)*a) 1 (terms n M-terms n N) x := by
  have hz k hk := diag_brush (M k-N k) j hx zero_lt_one |>.climb (show k.factorial*‖M k-N k‖*(1:ℝ)^k≤a by rw [one_pow,mul_one]; exact h k hk) (inv_one.le)
  have he := Brush.spree (Finset.range (n+1)) (fun k=> Tensor.diagonal (M k-N k)) (fun _=>a) (x:=x) zero_le_one (fun i hi=> hz i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  rw [Finset.sum_const,Finset.card_range, nsmul_eq_mul, Nat.cast_add,Nat.cast_one] at he
  refine he.shimmy (Eventually.of_forall fun y=>?_)
  simp only [terms,Pi.sub_apply,Finset.sum_apply]; rw [← Finset.sum_sub_distrib]; rfl

lemma t_sub_poly {f g:E→Y} (hg : ContDiffAt ℝ (↑j) g 0) (hf : ContDiffAt ℝ (↑j) f 0) (h : Brush j a 1 (f-g) 0) (hx : ‖x‖ ≤ 1) (k:ℕ) :
    Brush k ((j+1)*a) 1 (blockTaylor j f-blockTaylor j g) x := by
  let M k := Tensor.coeff f k 0; let N k:=Tensor.coeff g k 0
  refine term_brush M N x j ?_ hx k
  intro k hk; unfold M N Tensor.coeff; rw [←smul_sub,norm_smul,Real.norm_of_nonneg (by positivity),←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul,← iteratedFDeriv_sub_apply (hf.of_le (Nat.cast_le.mpr hk)) (hg.of_le (Nat.cast_le.mpr hk))]; exact (Brush.offer.1 h).inside k hk
end taylor

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {φ ψ : E × Body ι → ℝ} {ρ : E → Body ι} {M : E → Matrix ι ι ℝ}
variable {j k n : ℕ} {p c a u v D C : ℝ} {x:ℝ×E}
section use
variable (φ ψ ρ M)
def aggregation (n:ℕ) := terms n (moment φ ψ ρ M)
def connected (n:ℕ) := blockTaylor n (Real.log ∘ aggregation φ ψ ρ M n)
end use

lemma collect0 : aggregation φ ψ ρ M n 0=1:= by
  -- moment0 price needs finite dimension? omitted warning edit
  unfold aggregation terms; rw [Finset.sum_apply, Finset.sum_eq_single 0, moment0]; swap; · simp
  exact fun b _ hb => by simpa only [smul_zero,hb, not_false_eq_true, ne_eq, zero_pow, zero_smul] using Tensor.homogeneous (moment φ ψ ρ M b) 0 0 -- edit

lemma agree (hkn : k ≤ n) (hj : j ≤ k) : iteratedFDeriv ℝ j (connected φ ψ ρ M k) 0=
    iteratedFDeriv ℝ j (connected φ ψ ρ M n) 0 := by
  let f:= aggregation φ ψ ρ M; have he (k:ℕ):ContDiffAt ℝ (↑k) (f k) 0:= (terms_art (moment φ ψ ρ M)).contDiffAt.of_le le_top
  have hg (k:ℕ):ContDiffAt ℝ (↑k) Real.log (f k 0) := by rw [show f k 0=1 from collect0]; exact Real.contDiffAt_log.mpr one_ne_zero
  unfold connected; rw [blockTaylor_jets (hg k |>.comp 0 (he k)) _ hj,blockTaylor_jets (hg n|>.comp 0 (he n)) _ (hj.trans hkn)]; have hp : (k:WithTop ℕ∞)≤ (n: WithTop ℕ∞):= Nat.cast_le.mpr hkn
  exact jets_comp (he k) ((he n).of_le hp) (hg k) ((hg n).of_le hp) (collect0.trans (collect0.symm)) (fun i hi => terms_le _ hi hkn) (fun _ _=> rfl) j hj

/-- Already a polynomial representation; all lower truncations recovered **exactly**. -/
lemma recovers (hkn : k ≤ n) : blockTaylor k (connected φ ψ ρ M n)=connected φ ψ ρ M k := by
  conv_rhs => rw [connected]
  unfold blockTaylor; refine Finset.sum_congr rfl fun i hi=> ?_; have hh := Nat.le_of_lt_succ (Finset.mem_range.mp hi); unfold Tensor.coeff
  rw [← agree hkn hh,connected,blockTaylor_jets _ _ hh]; exact (Real.contDiffAt_log.mpr ((show aggregation φ ψ ρ M k 0≠0 from ne_of_eq_of_ne collect0 one_ne_zero))).comp _ ((terms_art (moment φ ψ ρ M)).contDiffAt.of_le le_top)

variable (h : Golf φ ψ ρ M j D u v p) (hD : 1 ≤ D)
local notation "μ" => sweep (M 0)⁻¹
include h
local notation "H" => ratify φ ψ ρ M D
local notation "U" => aggregation φ ψ ρ M
omit h
omit [FiniteDimensional ℝ E] in
lemma comparison0 [FiniteDimensional ℝ E]  (hg : Brush k a 1 (U k-blockTaylor k (H)) 0) (hp : ContDiffAt ℝ (↑k) H 0) :
    Brush k a 1 (U k-H) 0 := by
  have ht : ContDiffAt ℝ (↑k) (U k) 0 := (terms_art _).contDiffAt.of_le le_top
  apply Brush.offer.2; refine ⟨ht.sub hp,fun i hi=>?_⟩
  unfold normJ; have hv := (Brush.offer.1 hg).inside i hi; unfold normJ at hv; rw [iteratedFDeriv_sub_apply (ht.of_le (Nat.cast_le.mpr hi)) (blockTaylor_contDiff .. |>.contDiffAt), blockTaylor_jets hp _ hi] at hv
  rw [iteratedFDeriv_sub_apply (ht.of_le (Nat.cast_le.mpr hi)) (hp.of_le (Nat.cast_le.mpr hi))]; exact hv

lemma cumul_fee (hg : Brush k a 1 (H-U k) 0) (hu : a ≤ 1)
    {T A K : ℝ} (he : Brush k K 1 H 0) (hI : Brush k T 1 (fun z:ℝ=> z⁻¹) 1)
    (hF : 0 < H 0) (hh : Brush k A 1 Log.slope1 (H 0)) (hx : ‖x‖≤1) :
    let p := Log.t2 k (a*clump k (K+1) T)
    Brush j ((k+1)*Log.t2 k (p*clump k (1+Log.t2 k (1*clump k (K+1) T)) A)) 1
      (blockTaylor k (Real.log ∘ H)-connected φ ψ ρ M k) x := by
  intro p
  have ht': Brush k (K+1) 1 (U k) 0:= by
    have hv := he.separating (hg.climb hu le_rfl); exact hv.shimmy (Eventually.of_forall fun i=> by simp)
  have hv:= Log.same_price hg ht' hF collect0 hI hh
  set c := clump k (K+1) T; change Brush k (Log.t2 k (p * _)) _ _ _ at hv
  have he := Real.contDiffAt_log.mpr hF.ne' |>.comp 0 he.smooth; have he' := Real.contDiffAt_log.mpr (show U k 0≠0 from ne_of_eq_of_ne collect0 one_ne_zero) |>.comp 0 ht'.smooth
  refine t_sub_poly he' he (hv.climb ?_ le_rfl) hx j
  have hh' := (cl (c:=1) k ht'.nonneg hI.nonneg le_rfl).1
  have hc:0≤c:=hh'
  have hp: 0 ≤ p := by change 0≤ Log.t2 k (a*c); have hh:=hg.nonneg; unfold Log.t2; positivity
  have hP: p ≤ Log.t2 k (1*c) := by change Log.t2 k (a*c) ≤ _; unfold Log.t2; gcongr
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cm _ (by positivity) hh.nonneg (add_le_add le_rfl hP)) hp) (by positivity)
end YM.AllOrder.Local.Vote
