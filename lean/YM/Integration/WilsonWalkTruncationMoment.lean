import YM.Integration.WilsonWalkTruncation
import YM.Integration.WilsonWalkEndpointBias
import YM.Integration.WilsonLinkDisplacement
import YM.Integration.WilsonPhysicalKernelClock
import Mathlib.Analysis.MeanInequalities

/-! An all-order bound on the true tagged Wilson remainder, including bounded
outgoing tests that see the entire original field and its prediction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWalkTruncationMoment

open RG Lattice Wilson MeasureTheory Filter
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open FullQLocal.RenderedStep MatchingLedger.Compass.Income
open WilsonKernelCoupling WilsonWalkMatrixSecant WilsonWalkTruncation
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} (S : StepData c f)

private theorem indexed_sum {α : Type*} (v : α → ℝ) (l : List α) :
    (l.map v).sum = ∑ i : Fin l.length, v (l.get i) := by
  nth_rw 1 [←List.ofFn_get l]
  rw [List.map_ofFn,List.sum_ofFn]
  rfl

private theorem indexed_prod {α : Type*} (v : α → ℝ) (l : List α) :
    (l.map v).prod = ∏ i : Fin l.length, v (l.get i) := by
  nth_rw 1 [←List.ofFn_get l]
  rw [List.map_ofFn,List.prod_ofFn]
  rfl

private theorem amgm {k : ℕ} (hk : k ≠ 0) (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∏ i, v i ≤ (k:ℝ)⁻¹ * ∑ i, (v i)^k := by
  have hk' : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have H := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin k => (k:ℝ)⁻¹) (fun i => (v i)^k)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [hk']) (fun i _ => pow_nonneg (hv i) _)
  simp_rw [fun i => Real.pow_rpow_inv_natCast (hv i) hk] at H
  rwa [←Finset.mul_sum] at H

def distance (Q V : Config G c) (e : Edge (Site c)) : ℝ :=
  ‖G.mat (V e*(Q e)⁻¹)-1‖

private theorem continuous_distance (Q : Config G c) (e : Edge (Site c)) :
    Continuous (fun V => distance Q V e) := by
  exact ((G.continuous_mat.comp ((continuous_apply e).mul continuous_const)).sub continuous_const).norm

private theorem continuous_weight (b : ℝ) (Q : Config G c) :
    Continuous (fun V : Config G c => S.noise b Q V) := by
  unfold StepData.noise StepData.penaltyWeight
  fun_prop

private theorem weight_nonneg (b : ℝ) (Q V : Config G c) : 0 ≤ S.noise b Q V :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (inv_pos.mpr (S.penaltyZ_pos b)).le (Real.exp_pos _).le

/-- The original kth moment pays a product of k displacements with arbitrary
repeated edge labels. The normalized finite AM–GM weights sum to one. -/
theorem product (b : ℝ) (Q : Config G c) (n : ℕ) (M : ℝ)
    (hm : ∀ e, (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
      (V e*(Q e)⁻¹) ∂prior G c) ≤ M)
    (l : List (Edge (Site c))) (hl : l.length = n+1) :
    Integrable (fun V => S.noise b Q V * (l.map (distance Q V)).prod) (prior G c) ∧
    (∫ V, S.noise b Q V * (l.map (distance Q V)).prod ∂prior G c) ≤ M := by
  letI : IsFiniteMeasureOnCompacts (prior G c) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  let ρ := S.noise b Q
  let F (i : Fin l.length) (V : Config G c) := distance Q V (l.get i)
  let P (i : Fin l.length) (V : Config G c) := ρ V*(F i V)^l.length
  have hρ : Continuous ρ := continuous_weight S b Q
  have hF i : Continuous (F i) := continuous_distance Q _
  have hP (i : Fin l.length) : Integrable (P i) (prior G c) :=
    (hρ.mul ((hF i).pow l.length)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPM (i : Fin l.length) : (∫ V, P i V ∂prior G c) ≤ M := by
    simpa only [P,ρ,F,distance,hl,WilsonLinkDisplacement.amplitude] using hm (l.get i)
  have hS : Integrable (fun V => ∑ i, P i V) (prior G c) :=
    integrable_finsetSum _ fun i _ => hP i
  have hlen : l.length ≠ 0 := by omega
  have hlen' : (l.length:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hlen
  have hprod : Continuous (fun V : Config G c => (l.map (distance Q V)).prod) := by
    simp_rw [indexed_prod]
    exact continuous_finsetProd _ fun i _ => hF i
  refine ⟨(hρ.mul hprod).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  calc
    _ ≤ ∫ V, (l.length:ℝ)⁻¹ * (∑ i, P i V) ∂prior G c := by
      apply integral_mono_of_nonneg (ae_of_all _ fun V => mul_nonneg (weight_nonneg S b Q V)
        (List.prod_nonneg (fun a ha => by
          obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
          exact norm_nonneg _))) (hS.const_mul _) (ae_of_all _ fun V => ?_)
      change S.noise b Q V * (l.map (distance Q V)).prod ≤ (l.length:ℝ)⁻¹ * ∑ i, P i V
      rw [indexed_prod]
      have H := mul_le_mul_of_nonneg_left
        (amgm hlen (fun i => F i V) (fun _ => norm_nonneg _)) (weight_nonneg S b Q V)
      exact H.trans_eq (by dsimp only [P,ρ,F]; rw [←Finset.mul_sum]; ring)
    _ = (l.length:ℝ)⁻¹ * ∑ i, ∫ V, P i V ∂prior G c := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hP i)]
    _ ≤ (l.length:ℝ)⁻¹ * ∑ _i : Fin l.length, M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hPM i))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = M := by simp [hlen']

/-- The signed outgoing test may depend on the complete sampled field. -/
def paired (b : ℝ) (Q : Config G c) (x : Site c) (w : Walk) (n : ℕ) (ζ : Config G c → ℂ) : G.Mat :=
  ∫ V, S.noise b Q V • (ζ V • remainder V Q x w n) ∂prior G c

/-- A signed full-field probe is priced before integration. The probe can
vary with the whole sampled configuration. -/
theorem consume_debit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ) (Q : Config G c) (L : List (Edge (Site c))) (n : ℕ)
    (F : Config G c → E) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ V, ‖F V‖ ≤ B*debit (distance Q V) L (n+1))
    (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ e, (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
      (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖∫ V, S.noise b Q V • F V ∂prior G c‖ ≤ B*(L.length:ℝ)^(n+1)*M := by
  let l := List.sublistsLen (n+1) L
  let P (i : Fin l.length) (V : Config G c) := S.noise b Q V*((l.get i).map (distance Q V)).prod
  have hlength (i : Fin l.length) : (l.get i).length = n+1 :=
    List.length_of_sublistsLen (List.get_mem l i)
  have hP (i : Fin l.length) : Integrable (P i) (prior G c) ∧ (∫ V, P i V ∂prior G c) ≤ M :=
    product S b Q n M hm _ (hlength i)
  have hsum : Integrable (fun V => ∑ i, P i V) (prior G c) :=
    integrable_finsetSum _ fun i _ => (hP i).1
  have hmajor (V : Config G c) :
      ‖S.noise b Q V • F V‖ ≤ B * ∑ i, P i V := by
    rw [norm_smul,Real.norm_of_nonneg (weight_nonneg S b Q V)]
    refine (mul_le_mul_of_nonneg_left (hF V)
      (weight_nonneg S b Q V)).trans_eq ?_
    dsimp only [P]
    rw [←Finset.mul_sum,debit,indexed_sum]
    dsimp only [l]
    ring
  have hcount : (l.length:ℝ) ≤ (L.length:ℝ)^(n+1) := by
    dsimp only [l]
    rw [List.length_sublistsLen]
    exact_mod_cast Nat.choose_le_pow L.length (n+1)
  calc
    _ ≤ ∫ V, ‖S.noise b Q V • F V‖ ∂prior G c :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ V, B * ∑ i, P i V ∂prior G c :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hsum.const_mul B) (ae_of_all _ hmajor)
    _ = B * ∑ i, ∫ V, P i V ∂prior G c := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hP i).1)]
    _ ≤ B * ∑ _i : Fin l.length, M := mul_le_mul_of_nonneg_left (Finset.sum_le_sum
      (fun i _ => (hP i).2)) hB
    _ = B*(l.length:ℝ)*M := by simp [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hB) hM

theorem consume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ)
    (Q : Config G c) (x : Site c) (w : Walk) (n : ℕ)
    (F : Config G c → E) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ V, ‖F V‖ ≤ B*‖remainder V Q x w n‖) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ e, (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
      (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖∫ V, S.noise b Q V • F V ∂prior G c‖ ≤ B*(w.length:ℝ)^(n+1)*M := by
  rw [←length_occurrences x w]
  apply consume_debit S b Q (occurrences x w) n F B hB _ M hM hm
  intro V
  apply (hF V).trans
  apply mul_le_mul_of_nonneg_left _ hB
  have H := WilsonWalkTruncation.bound (V*Q⁻¹) Q x w n
  change ‖remainder V Q x w n‖ ≤ debit (fun e => ‖G.mat (V e*(Q e)⁻¹)-1‖) (occurrences x w) (n+1)
  simpa only [inv_mul_cancel_right,Pi.mul_apply,Pi.inv_apply] using H

theorem conditional (b : ℝ) (Q : Config G c) (x : Site c) (w : Walk) (n : ℕ)
    (ζ : Config G c → ℂ) (B : ℝ) (hB : 0 ≤ B) (hζ : ∀ V, ‖ζ V‖ ≤ B)
    (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ e, (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
      (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖paired S b Q x w n ζ‖ ≤ B*(w.length:ℝ)^(n+1)*M := by
  apply consume S b Q x w n (fun V => ζ V • remainder V Q x w n) B hB _ M hM hm
  intro V
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hζ V) (norm_nonneg _)

private theorem decode_bound (j : G.ColorIndex) (X : G.Mat) :
    ‖Comparison.Stencils.decode j X‖ ≤ (1/G.colorScale)*‖X‖ := by
  let Y := Pert.First.recoverL G X
  change ‖((Y j : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real,Real.norm_eq_abs]
  calc
    |Y j| = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) Y| := by
      simp only [EuclideanSpace.basisFun_inner]
    _ ≤ ‖Y‖ := (abs_real_inner_le_norm _ _).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
    _ ≤ _ := WilsonWalkEndpointBias.recover_bound X

/-- The actual oriented periodic color coordinate is expanded with its
original fixed real-linear curvature decoder. -/
def slotError (U Q : Config G c) (x : Site c) (s : Slot) (j : G.ColorIndex) (n : ℕ) : ℂ :=
  ((s.atSite U x j : ℝ) : ℂ) - Comparison.Stencils.decode j
    (jet U Q x (Comparison.Stencils.closes s) n)

theorem slot_read (U Q : Config G c) (x : Site c) (s : Slot) (j : G.ColorIndex) (n : ℕ) :
    slotError U Q x s j n = Comparison.Stencils.decode j
      (remainder U Q x (Comparison.Stencils.closes s) n) := by
  rw [remainder,map_sub,slotError,WilsonWalkEndpointBias.atSite_reads]
  rfl

/-- A decoded unmarked unitary letter word has size at most one in its
original physical color normalization. -/
theorem slot_unit (U : Config G c) (x : Site c) (s : Slot) (j : G.ColorIndex) :
    |s.atSite U x j| ≤ 1 := by
  let u := travel U x (Comparison.Stencils.closes s)
  have H := decode_bound j (G.mat u)
  have hu : ‖G.mat u‖ = G.colorScale := Gauge.unitary_frob (G.mat_mul_star u)
  rw [hu,one_div,inv_mul_cancel₀ G.colorScale_pos.ne'] at H
  rw [WilsonWalkEndpointBias.atSite_reads]
  change |Pert.First.recoverL G (G.mat u) j| ≤ 1
  change ‖((Pert.First.recoverL G (G.mat u) j : ℝ) : ℂ)‖ ≤ 1 at H
  rwa [Complex.norm_real,Real.norm_eq_abs] at H

/-- Every positive homogeneous layer obeys its own ordered occurrence debit.
On the final marked contact the remaining predicted path is unitary. -/
theorem layer_bound (g Q : Config G c) (x : Site c) (w : Walk) (n : ℕ) :
    ‖layer (g*Q) Q x w (n+1)‖ ≤ debit (fun e => ‖G.mat (g e)-1‖) (occurrences x w) (n+1) := by
  induction w generalizing x n with
  | nil => simp [layer,jet,occurrences,debit]
  | cons d w ih =>
    cases n with
    | zero =>
      rw [layer_cons,layer_zero,occurrences,debit_cons,debit_zero,mul_one]
      refine (norm_add_le ..).trans ?_
      rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul _),Gauge.frob_mul_eq _ _ (G.mat_mul_star _),increment_norm]
      exact add_le_add (ih (x+d.vec) 0) (le_refl ‖G.mat (g (d.used x))-1‖)
    | succ n =>
      rw [layer_cons,occurrences,debit_cons]
      refine (norm_add_le ..).trans (add_le_add ?_ ?_)
      · rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul _)]
        exact ih (x+d.vec) (n+1)
      · apply (norm_mul_le ..).trans
        rw [increment_norm]
        exact mul_le_mul_of_nonneg_left (ih (x+d.vec) n) (norm_nonneg _)

theorem slot_layer (g Q : Config G c) (x : Site c) (s : Slot) (j : G.ColorIndex) (n : ℕ) :
    let w := Comparison.Stencils.closes s
    ‖Comparison.Stencils.decode j (layer (g*Q) Q x w (n+1))‖ ≤
      (1/G.colorScale)*debit (fun e => ‖G.mat (g e)-1‖) (occurrences x w) (n+1) := by
  exact (decode_bound j _).trans (mul_le_mul_of_nonneg_left (layer_bound g Q x _ n)
    (div_nonneg zero_le_one G.colorScale_pos.le))

theorem slot_pointwise (g Q : Config G c) (x : Site c) (s : Slot) (j : G.ColorIndex) (n : ℕ) :
    ‖slotError (g*Q) Q x s j n‖ ≤ (1/G.colorScale)*debit (fun e => ‖G.mat (g e)-1‖)
      (occurrences x (Comparison.Stencils.closes s)) (n+1) := by
  rw [slot_read]
  exact (decode_bound j _).trans (mul_le_mul_of_nonneg_left (WilsonWalkTruncation.bound g Q x _ n)
    (div_nonneg zero_le_one G.colorScale_pos.le))

/-- The complex outgoing test multiplies the measured original decoded
coordinate, after its real-linear curvature projection. -/
theorem slot_conditional (b : ℝ) (Q : Config G c) (x : Site c) (s : Slot) (j : G.ColorIndex) (n : ℕ)
    (ζ : Config G c → ℂ) (B : ℝ) (hB : 0 ≤ B) (hζ : ∀ V, ‖ζ V‖ ≤ B)
    (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ e, (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
      (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖∫ V, S.noise b Q V • (ζ V * slotError V Q x s j n) ∂prior G c‖ ≤
      (B*(1/G.colorScale))*((s.length+s.walk.length:ℕ):ℝ)^(n+1)*M := by
  rw [←Comparison.Stencils.cost_path]
  apply consume S b Q x (Comparison.Stencils.closes s) n (fun V => ζ V * slotError V Q x s j n)
    (B*(1/G.colorScale)) (mul_nonneg hB (div_nonneg zero_le_one G.colorScale_pos.le)) _ M hM hm
  intro V
  rw [norm_mul,slot_read]
  exact (mul_le_mul (hζ V) (decode_bound j _) (norm_nonneg _) hB).trans_eq (mul_assoc ..).symm

/-- The measured signed tagged error permits a separate full outgoing test on
each real prediction. -/
def tagged (b : ℝ) (U : Config G f) (x : Site c) (w : Walk) (n : ℕ)
    (ζ : S.Choices → Config G c → ℂ) : G.Mat :=
  ∑ z, S.likelihood U z • paired S b (S.prediction U z) x w n (ζ z)

theorem mixture (b : ℝ) (h : S.patch.Branches S.kernel G) (U : Config G f)
    (x : Site c) (w : Walk) (n : ℕ) (ζ : S.Choices → Config G c → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hζ : ∀ z V, ‖ζ z V‖ ≤ B) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ z e, let Q := S.prediction U z
      (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
        (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖tagged S b U x w n ζ‖ ≤ B*(w.length:ℝ)^(n+1)*M := by
  unfold tagged
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ z, S.likelihood U z * (B*(w.length:ℝ)^(n+1)*M) := by
      apply Finset.sum_le_sum
      intro z _
      rw [norm_smul,Real.norm_of_nonneg (S.likelihood_pos U z)]
      exact mul_le_mul_of_nonneg_left (conditional S b _ x w n _ B hB (hζ z) M hM (hm z))
        (S.likelihood_pos U z)
    _ = _ := by rw [←Finset.sum_mul,S.chosen h U,one_mul]

/-- One genuine regulator tail controls all truncation orders, every cutoff,
period and finite walk, and all bounded signed outgoing tests on the same run. -/
theorem selected (R : Run G) (hG : G.Simple) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ (n : ℕ) (x : Site (R.family.side m p)) (w : Walk) (U : Config G (R.family.side (m+1) p)),
      let S := R.family.path.levels.clock.op m p
      let b := R.family.path.β N p (m+1)
      ∀ (ζ : S.Choices → Config G (R.family.side m p) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ z V, ‖ζ z V‖ ≤ B) →
      ‖tagged S b U x w n ζ‖ ≤ B*(w.length:ℝ)^(n+1)*C (n+1)*(regulatorRun R.family N p (m+1))^(n+1) := by
  obtain ⟨C,hC,H⟩ := WilsonLinkDisplacement.calendar R.family.path.levels.clock
  refine ⟨C,hC,?_⟩
  filter_upwards [WilsonPhysicalKernelClock.transport R hG H] with m hm N p hN n x w U
  dsimp only
  intro ζ B hB hζ
  let t := regulatorRun R.family N p (m+1)
  have ht : 0 ≤ t := (Weather.runs_pos R.family R.makes (Nat.succ_le_of_lt hN) p).le
  have htime := hm N p hN (n+1) m p
  rw [WilsonPhysicalKernelClock.temperature R N p (m+1) (Nat.succ_le_of_lt hN)] at htime
  have hmeasure := mixture (R.family.path.levels.clock.op m p) (R.family.path.β N p (m+1))
    (R.family.path.levels.blocks m p).branches U x w n ζ B hB hζ (C (n+1)*t^(n+1))
    (mul_nonneg (hC _) (pow_nonneg ht _)) (fun z e => htime e _)
  exact hmeasure.trans_eq (by dsimp only [t]; ring)

end YM.Integration.WilsonWalkTruncationMoment
end
