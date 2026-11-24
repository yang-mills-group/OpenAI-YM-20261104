import YM.PhysMS.Frame.Step
import YM.RG12.Roof.Echelons
import YM.OPE.Levy.Anchor

/-! # Subpower frame prices at *continuous measurement lengths*

In both directions. Use the previous coherence estimate for our same Final; these rates are not
estimates with logarithmic margin. They *are* enough to carry arbitrary small power loss estimates,
without assuming inhomogeneous parts are flat at any coupling order. (They are not an excuse for
multiplying this cost by a fixed perturbative comparison estimate when the latter is marginal.)
All-length tilt through the graded triangular towers via ShellIteration, i.e. an actual recurrence
on measured frames; no replication, no untracked change to the underlying Family or densities. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Set Filter Function Spec OPE OPE.Levy Climb Maxwell Trace.Pilot
open Extra.FD RG12.Roof
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "engine" a => Pert.Scale.gear C.labels d a
local notation "B₀" => recorded C.labels d

section growth
private def calibrationCost : ℝ := ∑ i, ‖(B₀).b i‖*‖((B₀).b.coord i).toContinuousLinearMap‖

private lemma calibration_bounds : 0 ≤ calibrationCost (C:=C) d := Finset.sum_nonneg fun i _=> by positivity
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

private lemma column_prices (Z : D →L[ℂ] Y) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ i, ‖Z ((B₀).b i)‖ ≤ A*‖(B₀).b i‖) : ‖Z‖ ≤ calibrationCost (C:=C) d * A := by
  refine Z.opNorm_le_bound (mul_nonneg (calibration_bounds d) hA) (fun v=>?_)
  let B:= B₀; let x(i):= B.b.coord i v
  rw [calibrationCost, Finset.sum_mul, Finset.sum_mul]; nth_rw 1 [← B.b.sum_repr v]; rw [map_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> ?_)
  rw [map_smul,norm_smul]; change ‖x i‖*‖Z _‖ ≤ _
  exact (mul_le_mul (((B₀).b.coord i).toContinuousLinearMap.le_opNorm v) (h i) (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring))

/-- No upward weight mixing has been assumed absent in the scaling U other than its compatibility
    with the actual filtration. Demand of grade e: OPE.Levy.planeAt starts at ⊥ for e=0;
    in particular this proves subpower control also of the WHOLE cap d matrix and unit mixing. -/
lemma plane_mask (e : ℕ)(he:e ≤ d)(i : Fin ((B₀).m+1))(r : ℝ)(hi : ((B₀).w i).1 < e)
    (h : ∀ c:ℕ, ∀ p:c≤d, ∀ v, J r d ((Free.scheme C.labels).rise p v) = F.sector.derivatives.rise p (J r c v)) :
    J r d ((B₀).b i) ∈ planeAt (U:=F.sector.derivatives) e he := by
  cases e with
  | zero => omega
  | succ k =>
    have he := (Nat.le_succ k).trans he
    obtain ⟨j,hj,hb⟩ := weighs_corner C.labels (B₀) i
    let Q := (C.labels.level d).basis j
    let x:= YM.UVNext.FreeStress.embed C.labels k
      ⟨Q.val,enough_height C.labels j (hb.trans_le (Nat.le_of_lt_succ hi))⟩
    have hx : (Free.scheme C.labels).rise he x=(B₀).b i:=by rw [hj]; exact UVNext.FreeStress.rise_embed _ _ (Free.scheme_filters C.labels) ..
    refine ⟨J r k x,?_⟩
    rw [← hx,h k he]

def pulling (φ : S.Field d →L[ℂ] Y) (r : ℝ) : D →L[ℂ] Y :=
    φ.comp ((J r d).toLinearMap.toContinuousLinearMap)

include H
private lemma forward (e : ℕ)(he:e ≤ d)(φ : S.Field d →L[ℂ] Y)(hf : ∀ p∈planeAt (U:=F.sector.derivatives) e he, φ p=0) :
    ∃ A:ℝ,1 ≤ A ∧ ∀ c:ℝ, 0 < c → c < 1 → ∀ᶠ r in trail, ∀ a∈Icc c 1,
          ‖pulling d J φ (a*r)‖ ≤ A*a^(e:ℝ)*‖pulling d J φ r‖ := by
  obtain ⟨u,hu,hU⟩:= comparison F d J H; let M:=calibrationCost (C:=C) d
  refine ⟨max (u*M) 1,le_max_right ..,fun c hc _=>?_⟩
  filter_upwards [hU c hc,eventually_all.mpr (fun i:Fin (d+1) => H.raised (Nat.le_of_lt_succ i.isLt))] with r hr he' t ht
  have hp := hc.trans_le ht.1; have hh (i:ℕ) (hi:i ≤ d) := he' (⟨i,Nat.lt_succ_of_le hi⟩:Fin (d+1))
  let X:= pulling d J φ r
  let z : D→L[ℂ] Y:= X.comp ((engine t).toContinuousLinearMap)
  have hz : ‖z‖ ≤ M*(t^e*‖X‖):= by
    refine column_prices d z (t^e*‖X‖) (by positivity) fun i=>?_
    let B:= (B₀); let j:= (B.w i).1
    rw [show z ((B₀).b i)= ((t:ℂ)^j) • X ((B₀).b i) from ?_]
    swap
    · change X ((engine t) ((B₀).b i))=_; rw [Pert.Scale.rare, map_smul]
    by_cases he : e ≤ j
    · rw [norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg hp.le,mul_assoc]
      exact mul_le_mul (pow_le_pow_of_le_one hp.le ht.2 he) (X.le_opNorm _) (norm_nonneg _) (by positivity)
    rw [show X ((B₀).b i)=0 from hf _ (plane_mask F d J _ (by assumption) i r (not_le.mp he) hh), smul_zero,norm_zero]; positivity
  rw [Real.rpow_natCast]
  apply (pulling d J φ (t*r)).opNorm_le_bound (_ : (0:ℝ)≤ _)
  · intro x; let y := cocycle d J r t hp x
    calc
       ‖_‖ = ‖z y‖ := congr_arg (fun k : S.Field d => ‖φ k‖) (cocycle_value d J x t r hp).symm
       _ ≤ ‖z‖ * ‖y‖ := z.le_opNorm y
       _ ≤ M*(t^e*‖X‖)*(u*‖x‖) := mul_le_mul hz ((hr t ht).1 x) (norm_nonneg _) (le_trans (norm_nonneg z) hz)
       _ = u*M*t^e*‖X‖*‖x‖:= by ring
       _ ≤ _:=(by gcongr; exact le_max_left ..)
  exact mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_right ..)) (by positivity)) (by positivity)

/-- Callers don't need a trajectory-aware Lodged frame witness here. -/
theorem upper (e : ℕ)(he:e ≤ d)(φ : S.Field d →L[ℂ] Y)(hf : ∀ p∈planeAt (U:=F.sector.derivatives) e he, φ p=0) :
    RateLE trail LogV (pulling d J φ) (-(e:ℝ)) := by
  obtain ⟨A,hA,h⟩:= forward F d J H e he φ hf
  exact shell_rate (pulling d J φ) hA h

def backward (r : ℝ) : S.Field d →L[ℂ] D:= LinearMap.toContinuousLinearMap (J r d).symm.toLinearMap
private lemma backward_step : ∃ A:ℝ,1 ≤ A ∧ ∀ c:ℝ, 0 < c → c < 1 → ∀ᶠ r in trail, ∀ a∈Icc c 1,
          ‖backward d J (a*r)‖ ≤ A*a^(-(d:ℝ))*‖backward d J r‖ := by
  obtain ⟨u,hu,hU⟩:= comparison F d J H; let M:=calibrationCost (C:=C) d
  refine ⟨max (u*M) 1,le_max_right ..,fun c hc _=>?_⟩
  filter_upwards [hU c hc] with r hr t ht
  have hp := hc.trans_le ht.1; let U:= backward d J r
  let z:D→L[ℂ]D:= LinearMap.toContinuousLinearMap (Pert.Scale.gear C.labels d t⁻¹)
  have hs:1≤ t⁻¹:= (one_le_inv₀ hp).mpr ht.2
  let A:= (t⁻¹)^d
  rw [Real.rpow_neg hp.le,Real.rpow_natCast,← inv_pow]; have hh : 0 ≤ u:=zero_le_one.trans hu; have ht : 0 ≤ M:= calibration_bounds d; have hA : 0≤ A:=by unfold A; positivity
  have hQ : ‖z‖ ≤ M*A := by
    refine column_prices d z A hA fun i=>?_; change ‖Pert.Scale.gear _ d t⁻¹ _‖≤_
    rw [Pert.Scale.rare,norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs ((B₀).cap i)) (norm_nonneg _)
  apply (backward d J (t*r)).opNorm_le_bound (by positivity); intro x; let b := cocycle d J r t hp
  have hx : b (backward d J (t*r) x)=z (U x):= by
    let y:= backward d J (t*r) x
    have he: (engine t) (b y)=U x:=by
      apply (J r d).injective; rw [show J r d _= _ from cocycle_value d J y t r hp, show J (t*r) d y=x from LinearEquiv.apply_symm_apply ..]; exact (LinearEquiv.apply_symm_apply ..).symm
    rw [← he]; exact (Pert.Scale.gear_inverse _ hp.ne' (b y)).symm
  calc
    _ = ‖b.symm (z (U x))‖ := by rw [← hx, b.symm_apply_apply]
    _ ≤ u*‖z (U x)‖:= (hr t (by assumption)).2 _
    _ ≤ u*(M*A*(‖U‖*‖x‖)) := mul_le_mul_of_nonneg_left ((z.le_opNorm _).trans (mul_le_mul hQ (U.le_opNorm _) (norm_nonneg _) (by positivity))) hh
    _ = u*M*A*‖U‖*‖x‖:=by ring
    _ ≤ _:=(by gcongr; exact le_max_left ..)

/-- Keep the output-to-moving-frame inverse; not inferring this from an uncontrolled norm
    of a fitted representation. -/
theorem inverse_rate : RateLE trail LogV (backward d J) (d:ℝ) := by
  obtain ⟨A,hA,h⟩:= backward_step F d J H
  simpa only [neg_neg] using (shell_rate (ζ:=-(d:ℝ)) (backward d J) hA h)
end growth
end YM.PhysMS.Frame
