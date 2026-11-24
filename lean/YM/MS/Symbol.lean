import YM.MS.Estimate
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Estimates of smoothed vertices and lines

Use native momentum throughout, so costs have a factor of `R^j` at every step.
Different momentum regions (for cover comparison and inside the zone of the physical
propagator) are accounted for by the Cost window. j bounds are not uniform in j.
Also at negative log time (UV in smoothing) we use `R>0` but it may be <1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real
open scoped ContDiff
variable {ι ι' E F G H W α : Type*}

structure Scale (ι : Type*) where
  length : ι → ℝ
  pos i : 0 < length i
  basic : ι → ℝ
  one_le i : 1 ≤ basic i

namespace Scale
variable (S : Scale ι) [NormedAddCommGroup E]

def weight i (p : E) := 1 + S.length i * ‖p‖

lemma one_le_weight i (p : E) : 1 ≤ S.weight i p := le_add_of_nonneg_right (mul_nonneg (S.pos i).le (norm_nonneg _))

lemma weight_pos i (p : E) : 0 < S.weight i p := zero_lt_one.trans_le (S.one_le_weight i p)

@[simp] lemma weight_zero i : S.weight i (0:E) = 1 := by simp [weight]

lemma basic_pos i : 0 < S.basic i := zero_lt_one.trans_le (S.one_le i)

def full : Cost ι E := ⟨fun _ => univ, fun i p => S.basic i * S.weight i p,
  fun i p _ => one_le_mul_of_one_le_of_one_le (S.one_le i) (S.one_le_weight i p)⟩

lemma weight_L {F} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℝ E]
    (L : E →L[ℝ] F) (i) p : S.weight i (L p) ≤ (1+‖L‖) * S.weight i p := by
  have hR := S.pos i; have := mul_le_mul_of_nonneg_left (L.le_opNorm p) hR.le
  unfold weight; nlinarith [mul_nonneg hR.le (norm_nonneg p), norm_nonneg L]
end Scale

variable (S : Scale ι)
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (T : Cost ι E)

abbrev Kern (ι E F : Type*) := ι → E → F

def Cost.Part (T : Cost ι E) (S : Scale ι) (f : Kern ι E F) (g : Kern ι E ℝ) (j : ℕ) :=
  T.Le (fun i p => ‖iteratedFDeriv ℝ j (f i) p‖) (fun i p => g i p*S.length i^j)

/-- Smooth in the second slot. No bound outside `T.zone`. -/
structure Costs (T : Cost ι E) (S : Scale ι) (f : Kern ι E F) (g : Kern ι E ℝ) : Prop where
  smooth (i : ι) : ContDiff ℝ ∞ (f i)
  quoted (j : ℕ) : T.Part S f g j

abbrev Bound (f : Kern ι E F) (g : ι → ℝ) := Costs S.full S f (fun i _ => g i)

section linear
variable {T S} {f f' : Kern ι E F} {g g' : Kern ι E ℝ}

lemma Cost.Part.nonneg (j : ℕ) (h : T.Part S f g j) : T.NN g :=
  fun i p hx => nonneg_of_mul_nonneg_left (Cost.nn_of_le h (fun _ _ _ => norm_nonneg _) i p hx) (pow_pos (S.pos i) _)

namespace Costs
lemma nonneg (h : Costs T S f g) : T.NN g := Cost.Part.nonneg 0 (h.quoted _)

protected lemma zero (h : T.NN g) : Costs T S (0 : Kern ι E F) g where
  smooth _ := contDiff_const
  quoted j := Cost.of_le fun i p hx => by
    simpa using mul_nonneg (h i p hx) (pow_nonneg (S.pos _).le j)

lemma norm_cost (hf : Costs T S f g) : T.Le (fun i p => ‖f i p‖) g := by
  simpa [Cost.Part] using hf.quoted 0

protected lemma add (hf : Costs T S f g) (he : Costs T S f' g) :
    Costs T S (fun i p => f i p + f' i p) g where
  smooth i := (hf.smooth i).add (he.smooth i)
  quoted j := by
    have h := Cost.Le.add (hf.quoted j) (he.quoted j) fun i p hx => mul_nonneg (hf.nonneg i p hx) (pow_nonneg (S.pos _).le _)
    refine h.left fun i p _ => ?_
    change ‖iteratedFDeriv ℝ j (f i + f' i) p‖ ≤ _
    rw [iteratedFDeriv_add ((hf.smooth _).of_le (by exact_mod_cast le_top)) ((he.smooth _).of_le (by exact_mod_cast le_top)), Pi.add_apply]; exact norm_add_le ..

lemma raise (hf : Costs T S f g) (h : T.Le g g') : Costs T S f g' where
  smooth := hf.smooth
  quoted j := (Cost.Le.trans (hf.quoted j) (h.cancel (fun i _ _ => pow_nonneg (S.pos i).le j)))

protected lemma sum (s : Finset α) {f : α → Kern ι E F} (hf : ∀ i ∈ s, Costs T S (f i) g) (hg : T.NN g) :
    Costs T S (fun i p => ∑ a ∈ s, f a i p) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact Costs.zero (F:=F) (S:=S) hg
  | insert a s ha ih => simpa [ha] using (hf a (Finset.mem_insert_self ..)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

protected lemma neg (hf : Costs T S f g) : Costs T S (fun i p => - f i p) g where
  smooth i := (hf.smooth i).neg
  quoted j := Cost.Le.left (hf.quoted j) (fun i p _ => by change ‖iteratedFDeriv ℝ j (- (f i)) p‖ ≤ _; rw [iteratedFDeriv_neg_apply, norm_neg])

protected lemma sub (hf : Costs T S f g) (hf' : Costs T S f' g) : Costs T S (fun i p => f i p - f' i p) g := by
  simpa only [sub_eq_add_neg] using hf.add hf'.neg

lemma L (A : F →L[ℝ] G) (hf : Costs T S f g) : Costs T S (fun i p => A (f i p)) g where
    smooth i := A.contDiff.comp (hf.smooth i)
    quoted j := (Cost.Le.const_mul (hf.quoted j) ‖A‖ (norm_nonneg _) (Cost.nn_of_le (hf.quoted j) (fun _ _ _ => norm_nonneg _))).left fun i p _ => by
      exact A.norm_iteratedFDeriv_comp_left ((hf.smooth i).contDiffAt) (by exact_mod_cast le_top)

protected lemma bilinear {u : Kern ι E W} (A : F →L[ℝ] W →L[ℝ] H) (hf : Costs T S f g) (hu : Costs T S u g') :
    Costs T S (fun i p => A (f i p) (u i p)) (fun i p => g i p * g' i p) where
  smooth i := A.isBoundedBilinearMap.contDiff.comp ((hf.smooth i).prodMk (hu.smooth i))
  quoted j := by
    let F' (k : ℕ) := fun i p => (j.choose k:ℝ)*‖iteratedFDeriv ℝ k (f i) p‖ * ‖iteratedFDeriv ℝ (j-k) (u i) p‖
    let R i p := g i p*g' i p*S.length i^j
    have hR : T.NN R := fun i p hx => mul_nonneg (mul_nonneg (hf.nonneg i p hx) (hu.nonneg i p hx)) (pow_nonneg (S.pos _).le _)
    have h (k : ℕ) (hk : k ∈ Finset.range (j+1)) : T.Le (F' k) R := by
      have hle : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hm := Cost.Le.mul (hf.quoted k) (hu.quoted (j-k)) (fun _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _)
      refine Cost.Le.left (Cost.Le.const_mul (Cost.Le.right hm (u:=R) (fun i p _ => ?_)) (j.choose k : ℝ) (by positivity) hR) fun i p _ => (mul_assoc _ _ _).le
      unfold R; conv_rhs => rhs; arg 2; rw [← Nat.add_sub_of_le hle]
      rw [pow_add]; ring_nf; rfl
    refine ((Cost.Le.finset_sum (Finset.range (j+1)) h hR).const_mul ‖A‖ (norm_nonneg A) hR).left fun i p _ => ?_
    exact A.norm_iteratedFDeriv_le_of_bilinear (hf.smooth i) (hu.smooth i) p (by exact_mod_cast le_top)

protected lemma mul {f f' : Kern ι E ℂ} (hf : Costs T S f g) (hf' : Costs T S f' g') :
    Costs T S (fun i p => f i p * f' i p) (fun i p => g i p*g' i p) :=
  Costs.bilinear (ContinuousLinearMap.mul ℝ ℂ) hf hf'

protected lemma linear {D : Cost ι G}
    (A : G →L[ℝ] E) (hf : Costs T S f g) (hm : ∀ i, MapsTo A (D.zone i) (T.zone i))
    (hp : D.Le (fun i p => T.cheap i (A p)) fun _ _ => 1) :
    Costs D S (fun i p => f i (A p)) (fun i p => g i (A p)) where
  smooth i := (hf.smooth i).comp A.contDiff
  quoted j := by
    let U i p := ‖iteratedFDeriv ℝ j (f i) (A p)‖
    have h := Cost.Le.pull (φ:=_root_.id) (ψ:=fun _ p => A p) (hf.quoted j) hm hp (fun i p hx => mul_nonneg (hf.nonneg i p hx) (pow_nonneg (S.pos i).le _))
    refine (h.const_mul (‖A‖^j) (by positivity) (fun i p hx => mul_nonneg (hf.nonneg i _ (hm i hx)) (pow_nonneg (S.pos i).le j))).left fun i p _ => ?_
    change ‖iteratedFDeriv ℝ j ((f i) ∘ A) p‖ ≤ _
    rw [A.iteratedFDeriv_comp_right]
    · simp only [id_eq, mul_comm (‖A‖ ^ j)]
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ j (f i) (A p)) (fun _ => A)
    exact (hf.smooth i)
    exact mod_cast le_top
end Costs
namespace Bound
variable {a b : ι → ℝ}
lemma linear {f : Kern ι E F} (A : W →L[ℝ] E) (h : Bound S f a) :
    Bound S (fun i p => f i (A p)) a := by
  refine Costs.linear (D:=S.full) A h (fun _ _ _ => Set.mem_univ _) ?_
  refine ⟨(1+‖A‖), by positivity, 1, fun i p _ => ?_⟩
  dsimp only [Scale.full]; rw [pow_one,mul_one]
  apply (mul_le_mul_of_nonneg_left (S.weight_L A i p) (S.basic_pos i).le).trans
  exact (mul_left_comm _ _ _).le
end Bound
end linear
end YM.MS
