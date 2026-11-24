import YM.Integration.SignedTreeOperator
import YM.Pert.Scale.Adjust

/-! The original perturbative engineering dilation on the physical quotient
recombines the homogeneous input words into the actual finite Wilson
observable for arbitrary fields with support in several dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedTreeDilation
open Function Filter Set Spec OPE OPE.Orbits PhysMS Wilson MeasureTheory FVA2
open Pert.Position Pert.Scale Maxwell Maxwell.Free MSbar.OPE RG11.Fields RG11.Grove RG11.Neighborhood
open OPETreeRemainder SignedTreeTransport SignedTreeOperator
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {S : Table C.book} {n m i d : ℕ}

/-- Each basis vector uses its own native engineering grade in the
already defined physical dilation. -/
theorem gear_basis (F : Labels.Frames G) (a : lab F i) (t : ℝ) :
    Pert.Scale.gear F i t ((tower F i).b a) =
      (t : ℂ)^(RG11.Window.grade F i a) • (tower F i).b a := by
  let A := tower F i
  rw [← Pert.RawLabels.physical_round F (A.b a), gear_inherit,
    grow_weights (w := RG11.Window.grade F i a)
      (p := Pert.RawLabels.physicalLabel F i (A.b a)) (fun b hb => ?_) t, map_smul]
  exact congrArg Prod.fst ((Labels.weight_slot b).symm.trans
    ((Labels.pure_grade _ _ |>.mp (basis_label A a)) hb))

variable (J : ℝ → PhysMS.tower S) (x : conf n) (y : Tail m) (H : ℕ)

/-- Original unscaled input fields with the dimension-adjusted, finite
independent MS tree output. Its argument is an arbitrary field tuple. -/
def unscaled (r t : ℝ) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) (N p : ℕ) :
    Config G (C.side N p) → ℂ := fun U =>
  observable J r (driven t x.val y) v w N p U -
    ∑ k ∈ Finset.range (H+1), (t : ℂ)^k * observable J r (close y)
      (fun _ : Fin 1 => output C.labels x (Pert.Scale.gear C.labels i t⁻¹ ∘ v) k) w N p U

/-- The scale-normalized cluster field is the native engineering dilation
of each input field. The independent MS output uses the unaltered fields. -/
def grouped (r t : ℝ) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) (N p : ℕ) :
    Config G (C.side N p) → ℂ := fun U =>
  observable J r (driven t x.val y) (Pert.Scale.gear C.labels i t ∘ v) w N p U -
    ∑ k ∈ Finset.range (H+1), (t : ℂ)^k *
      observable J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p U

theorem unscaled_eq (r t : ℝ) (ht : t ≠ 0) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d)
    (N p : ℕ) : unscaled J x y H r t v w N p =
      grouped J x y H r t (Pert.Scale.gear C.labels i t⁻¹ ∘ v) w N p := by
  have h : Pert.Scale.gear C.labels i t ∘ (Pert.Scale.gear C.labels i t⁻¹ ∘ v) = v := by
    funext b
    simpa only [inv_inv,Function.comp_apply] using gear_inverse C.labels (s := t⁻¹) (inv_ne_zero ht) (v b)
  exact congrArg (fun z : Fin n → E C.labels i => fun U =>
    observable J r (driven t x.val y) z w N p U -
      ∑ k ∈ Finset.range (H+1), (t : ℂ)^k * observable J r (close y)
        (fun _ : Fin 1 => output C.labels x (Pert.Scale.gear C.labels i t⁻¹ ∘ v) k) w N p U) h.symm

def action (T : Table C.book) (r t : ℝ) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i)
      (MultilinearMap ℂ (fun _ : Fin m => E C.labels d) ℂ) :=
  (SignedTreeTensor.pair T J r (driven t x.val y)).compLinearMap
    (fun _ => Pert.Scale.gear C.labels i t) -
  ∑ k ∈ Finset.range (H+1), (t : ℂ)^k • (replacement T J r y k d).compMultilinearMap
    (SignedTreeTensor.coefficient C.labels x k)

theorem on_basis (T : Table C.book) (r t : ℝ) (u : sheaf C.labels n i)
    (w : Fin m → E C.labels d) : action J x y H T r t ((tower C.labels i).b ∘ u) w =
    tensor J x y (RG11.Window.grade C.labels i ∘ u) H T r t ((tower C.labels i).b ∘ u) w := by
  let b := (tower C.labels i).b
  let g := RG11.Window.grade C.labels i
  have h : (fun j => Pert.Scale.gear C.labels i t ((b ∘ u) j)) =
      (fun j => (t : ℂ)^(g (u j)) • b (u j)) := funext (fun j => gear_basis C.labels (u j) t)
  simp only [action,tensor,_root_.sub_apply,MultilinearMap.compLinearMap_apply,_root_.smul_apply]
  rw [h, MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
  rfl

theorem grouped_continuous (r t : ℝ) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d)
    (N p : ℕ) : Continuous (grouped J x y H r t v w N p) :=
  (observable_continuous J r (driven t x.val y) (Pert.Scale.gear C.labels i t ∘ v) w N p).sub
    (continuous_finsetSum _ fun k _ =>
      (observable_continuous J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p).const_mul _)

theorem grouped_mean (r t : ℝ) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) (N p : ℕ) :
    moment (C.beta N p) (grouped J x y H r t v w N p) =
      moment (C.beta N p) (observable J r (driven t x.val y) (Pert.Scale.gear C.labels i t ∘ v) w N p) -
        ∑ k ∈ Finset.range (H+1), (t : ℂ)^k * moment (C.beta N p)
          (observable J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p) := by
  let μ := law G (C.side N p) (C.beta N p)
  let b k := observable J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p
  have hb (k : ℕ) : Integrable (fun U => (t : ℂ)^k * b k U) μ :=
    (continuous_integrable _ (observable_continuous J r _ _ w N p)).const_mul _
  have ha := continuous_integrable (C.beta N p) (observable_continuous J r (driven t x.val y)
    (Pert.Scale.gear C.labels i t ∘ v) w N p)
  change (∫ U, _ - ∑ k ∈ Finset.range (H+1), (t : ℂ)^k * b k U ∂μ) = _
  rw [integral_sub ha (integrable_finsetSum _ fun k _ => hb k),
    integral_finsetSum _ fun k _ => hb k]
  simp_rw [integral_const_mul]
  rfl

theorem action_finite (hC : C.Makes) (r t : ℝ) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d)
    (N p j : ℕ) (hj : j ≤ N) : action J x y H (StressFlux.Matching.rounded C N p) r t v w =
      mean C N p j hj (grouped J x y H r t v w N p) := by
  rw [mean_eq hC _ _ _ _ _ (grouped_continuous ..), grouped_mean]
  simp only [action, _root_.sub_apply, _root_.smul_apply, _root_.sum_apply,
    MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply, replacement_apply,
    SignedTreeTensor.coefficient_apply, SignedTreeTensor.finite_pair, smul_eq_mul]
  rfl

end YM.Integration.SignedTreeDilation
