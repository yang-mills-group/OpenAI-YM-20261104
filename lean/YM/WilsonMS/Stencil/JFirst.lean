import YM.WilsonMS.Stencil.JRad
/-!
# J dictionary at the free specialization

Check against the MS target bivariant on-shell stencil symbols. No metadata
matching/invented methods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.JRad
open Function Filter Set Finset MeasureTheory
open MS Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Rock _root_.YM.MS.Shine Outlook
open MvPolynomial Labels Analysis Tensor Maxwell Motif Halo Mach Lifting Theater HBeam Detect
  Detect.Mark Local.BV InnerProductSpace
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {m n k i j : ℕ} {z : ℂ} {a b c : Axis}
section curl

def curlX (a b : Axis) : Feet G (i + 1) →ₗ[ℝ] Tensor.T E4 G.Color i
    where
  toFun F := (stepL G Axis i a F).val b - (stepL G Axis i b F).val a
  map_add' F H := by
    ext1 v
    simp
    abel
  map_smul' t F := by
    ext1 v
    simp [smul_sub]

lemma gradient_0 (F : Head G (i + 2)) (a b : Axis) : curlX a b (gradS G (i + 1) F) = 0 := by
  let H := (F.val ())
  let x := basis a
  let y := basis b
  apply ContinuousMultilinearMap.ext
  intro v
  let Y := H (Fin.cons y (Fin.cons x v))
  let X := H (Fin.cons x (Fin.cons y v))
  suffices he : Y = X
    by
    change (i + 1 : ℝ) • ((Nat.cast (R := ℝ) (i + 1) + 1) • Y) - _ = _
    rw [he]
    exact sub_self _
  have he : (Fin.cons x (Fin.cons y v)) ∘ Equiv.swap 0 1 = Fin.cons y (Fin.cons x v) := by
    ext1 j
    refine Fin.cases ?_ (fun m => Fin.cases ?_ (fun i => ?_) m) j <;>
      first
      | (solve
          | simp [Equiv.swap_apply_def])
      | ( simp [Equiv.swap_apply_def]
          rw [if_neg
              (show i.succ.succ ≠ 1 from
                (show i.succ.succ ≠ (0 : Fin (_ + 1)).succ from fun q =>
                  Fin.succ_ne_zero _ (Fin.succ_inj.mp q)))]
          simp)
  change H _ = H _
  rw [← he]
  apply F.property _

lemma houses_curl (F : Feet G (i + 1)) (a b : Axis) : takeCurl (yard G i F) a b = curlX a b F := by
  have ht (A : Labels.Taylor G i) : curlX a b (step_in G i A) = takeCurl A a b := by
    change
      ((i + 1 : ℝ) • (A.val b).curryLeft (basis a) - (i + 1 : ℝ) • (A.val a).curryLeft (basis b)) = _
    rw [takeCurl, Nat.cast_add, Nat.cast_one, smul_sub]
  rw [← ht, taxiY, carveΩ, map_sub, map_smul, gradient_0, smul_zero, sub_zero]
end curl

lemma spotlight (x : E4) (p : SectorP 0) : (∑ i : Axis, x i * p i) = inner ℝ (fixF p) x := by
  nth_rw 2 [←
    show ∑ i : Axis, x i • basis i = x from by
      ext
      simp]
  simp only [inner_sum, inner_smul_right, lean_axis]

lemma ray_floor (p : SectorP 0) (x : E4) (a b : Axis) (v : Cfield G 0) (c : G.ColorIndex) (i : ℕ) :
    rayF 0 x a b i c [(v, p)] =
      (I * (inner ℝ (fixF p) x : ℂ)) ^ i * F₀ (chair 0 a) (chair 0 b) c [(v, p)] := by
  induction i with
  | zero => simp [rayF, cur]
  | succ i ih =>
    rw [rayF, pow_succ']
    change direction G 0 0 x (rayF 0 x a b i) c _ = _
    rw [direction, LinearMap.sum_apply]
    simp only [Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, convoke, zero_smul,
      add_zero, axisP, lock, rowP, moon, ih]
    rw [← spotlight, pow_succ, Complex.ofReal_sum]
    rw [show net ([(v, p)]) = p from
        (by
          change p + 0 = _
          rw [add_zero])]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [spike_δ]
    unfold spikeV
    push_cast
    rw [show chair 0 j = j from rfl]
    ring

lemma cash_p (p : FourP) (x : E4) (a b : Axis) (c : G.ColorIndex) (v : G.ColorIndex) (u : Axis)
    (i : ℕ) :
    let K := yard G i (speak (i + 1) u p (cl G v));
    Theater.amount i • rayF 0 x a b i c [(at_g (chair 0 u) v, (p : SectorP 0))] =
      hitϑ (i + 1) * ((Tensor.diagonal (takeCurl K a b) x c : ℝ) : ℂ) := by
  intro K
  rw [ray_floor, f_ref]
  let H := inner ℝ (fixF p) x
  let J := Theater.amount i • (H ^ i • cl G v)
  have hh (a : Axis) : (speak i u p (cl G v)).val a (fun _ => x) = if a = u then J else 0 := by
    split_ifs with h
    rw [h, speak, wearing]
    simp only [Finset.prod_const, card_univ, Fintype.card_fin]
    rfl
    rw [speak, Theater.away _ _ _ h]
    rfl
  have he :
    Tensor.diagonal (takeCurl K a b) x =
      p a • (if b = u then J else 0) - p b • (if a = u then J else 0) := by
    unfold K
    rw [houses_curl]
    change (stepL _ _ _ a _).val b _ - (stepL _ _ _ b _).val a _ = _
    rw [step_at, step_at]
    simp [hh]
  rw [he]
  unfold J
  simp only [show ∀ q : Axis, chair 0 q = q from fun _ => rfl]
  by_cases hx : v = c <;> by_cases ha : a = u <;> by_cases hb : b = u <;>
      simp [Landau.delta, ha, hb, hx, H, cl, Complex.real_smul, hitϑ, mul_pow] <;>
    ring

lemma not_conn (p : SectorP 0) (x : E4) (a : Axis) (v : Cfield G 0) (c : G.ColorIndex) (i : ℕ)
    (h : ∀ i j, v ≠ at_g i j) : node 0 a i x c [(v, p)] = 0 := by
  simp only [node, Pi.smul_apply, Finset.sum_apply, ray_floor, c_α, if_neg (h _ _), mul_zero,
    sub_zero, smul_zero, Finset.sum_const_zero]

lemma node_1 (p : SectorP 0) (x : E4) (a : Axis) (c : G.ColorIndex) (i : ℕ) (v : G.ColorIndex)
    (u : Axis) :
    node 0 a i x c [(at_g (chair 0 u) v, p)] =
      hitϑ (i + 1) * ((Labels.Taylor.value (yard G i (speak (i + 1) u p (cl G v))) a x c : ℝ) : ℂ) := by
  let K := yard G i (speak (i + 1) u p (cl G v))
  rw [show (yard G i (speak (i + 1) u p (cl G v))).value a x = _ from
      Eq.trans (congr_arg (fun z : Labels.Taylor G i => z.value a x) (potential_recover K).symm)
        (contracted_diag (closedCurl K) a x)]
  push_cast
  simp only [node, Pi.smul_apply, Finset.sum_apply, Finset.smul_sum]
  simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp := cash_p p x k a c v u i
  change _ = _ * (((Tensor.diagonal (takeCurl K _ _) x) c : ℝ) : ℂ) at hp
  rw [Complex.real_smul] at hp
  rw [volume, mul_inv, Complex.ofReal_mul,
    show ((Nat.factorial i : ℝ)⁻¹ : ℝ) = Theater.amount i from rfl]
  unfold Theater.amount at hp
  push_cast at *
  linear_combination (((i : ℂ) + 2)⁻¹ * (x k : ℂ)) * hp

lemma measuring (x : E4) (a : Axis) (c : G.ColorIndex) (i : ℕ) :
    factor G i (reading G i x a c) 0 0 =
      Koszul.mono (RowLeg G i (Complex.ofRealCLM.toLinearMap.comp (reading G i x a c))) := by
  rw [corresponding]
  funext l
  by_cases h : l.length = 1
  swap
  · rw [show node 0 a i x c l = 0 from ?_]
    rcases l with _ | ⟨k, _ | _⟩ <;>
      first
      | rfl
      | simp at h
    simp only [node, ray_sum, Pi.smul_apply, Finset.sum_apply,
      show ∀ k k' (l' : List Axis), Pole G 0 k k' 0 l' c l = 0 from fun k k' l' =>
          Pole.rank0 k k' l' c l
            (by
              rw [Book.mod_int]
              omega),
      smul_zero, Finset.sum_const_zero]
  obtain ⟨⟨t, p⟩, rfl⟩ := List.length_eq_one_iff.mp h
  rcases t with ⟨⟨_ | b, H⟩, v⟩
  · exact not_conn p x a _ c i (fun i j h => by simp [at_g] at h)
  cases H
  · exact node_1 p x a c i v b
  exact not_conn p x a _ c i (fun i j h => by simp [at_g] at h)

lemma first_line (f : Module.Dual ℝ (Labels.Taylor G i)) :
    factor G i f 0 0 = Koszul.mono (RowLeg G i (Complex.ofRealCLM.toLinearMap.comp f)) := by
  let R (g : Module.Dual ℝ (Labels.Taylor G i)) := RowLeg G i (Complex.ofRealCLM.toLinearMap.comp g)
  have he : f ∈ Submodule.span ℝ {g | ∃ x a c, g = reading G i x a c} := by
    rw [JRad.enough]
    exact Submodule.mem_top
  refine
    Submodule.span_induction (p := fun g _ => factor G i g 0 0 = Koszul.mono (R g)) ?_ ?_ ?_ ?_ he
  · rintro f ⟨x, a, c, rfl⟩
    exact measuring x a c i
  · simp only [map_zero, R, LinearMap.comp_zero, Pi.zero_apply]
    funext l
    rcases l with _ | ⟨i, _ | l⟩ <;> rfl
  · intro a b ha hb ht hx
    rw [map_add, Pi.add_apply, Pi.add_apply, ht, hx,
      show R (a + b) = R a + R b by
        unfold R
        rw [← map_add]
        congr 1
        ext
        simp]
    funext l
    rcases l with _ | ⟨i, _ | l⟩ <;> simp [mono]
  intro c a h hx
  rw [map_smul, Pi.smul_apply, Pi.smul_apply, hx, show R (c • a) = (c : ℂ) • R a from ?_]
  · funext l
    rcases l with _ | ⟨i, _ | l⟩ <;> simp [mono]
  unfold R
  rw [← map_smul]
  congr 1
  ext j
  simp
end YM.WilsonMS.JRad
