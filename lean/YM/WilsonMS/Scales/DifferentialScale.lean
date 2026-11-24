import YM.WilsonMS.Scales.BetaConj
import Mathlib.RingTheory.PowerSeries.Derivative
/-!
# Formal beta-functions from the intrinsic dilation group

Expose generator data based only on the length-one reports, not a kinetic
solver at numerical coupling. Smooth and carries scale law for converted
comparison fields. Not about explicit coefficients (one-loop extraction
not addressed here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Datum
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC GFlow
open scoped BigOperators Topology Classical ContDiff PowerSeries
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G

lemma contD {p : ℝ → ℂ} (h : Ready p) : ContDiff ℝ ⊤ p := by
  obtain ⟨n, h⟩ := h
  rw [funext (interpret h)]
  unfold Logarithm.evaluate
  apply ContDiff.sum
  intro i hi
  refine
    ContDiff.smul (f := fun x : ℝ => Polynomial.eval x (plate n i)) (g := fun _ => p (↑i : ℝ)) ?_
      contDiff_const
  simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) (plate n i) ⊤
variable {p q : ℝ → Cn}

abbrev speed (p : ℝ → Cn) :=
  ∀ n, Ready fun t => coeff n (p t)

lemma speed.power (h : speed p) (n : ℕ) : speed (fun t => p t ^ n) := by
  induction n with
  | zero =>
    simp_rw [pow_zero]
    intro n
    exact Ready.const _
  | succ k ih =>
    simp_rw [pow_succ]
    intro n
    simp_rw [PowerSeries.coeff_mul]
    exact accounts _ fun i _ => Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (ih _) (h _)

lemma speed.const (p : Cn) : speed (fun _ => p) := fun _ => Ready.const _

lemma speed.reexpress (h : speed p) (ht : speed q) (hv : ∀ i, Rooted (q i)) :
    speed (fun t => (p t).subst (q t)) := by
  intro n
  simp_rw [usePool (hv _)]
  exact accounts _ fun i _ => Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (speed.power ht i n) (h i)
section chain

variable {p : ℝ → Cn} {P Q : Cn} {F F' : ℝ → Cn}

def Giving (F : ℝ → Cn) (P : Cn) (x : ℝ) :=
  ∀ n, HasDerivAt (fun t => coeff n (F t)) (coeff n P) x

lemma Giving.prod {x : ℝ} (hp : Giving F P x) (hq : Giving F' Q x) :
    Giving (fun i => F i * F' i) (P * F' x + F x * Q) x := by
  intro i
  simp_rw [PowerSeries.coeff_mul, map_add, PowerSeries.coeff_mul, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum (fun i _ => (hp i.1).mul (hq i.2))

lemma Giving.pre {x : ℝ} {F H : Cn} (h : Rooted F) (hp : Giving p H x) :
    Giving (fun i => (p i).subst F) (H.subst F) x := by
  intro j
  simp_rw [usePool h]
  exact HasDerivAt.fun_sum (fun i _ => (hp i).const_mul _)

def Beta (p : ℝ → Cn) :=
  PowerSeries.mk (fun n => deriv (fun i => coeff n (p i)) (0 : ℝ))

lemma certBeta (h : speed F) : Giving F (Beta F) 0 := by
  intro i
  rw [Beta, PowerSeries.coeff_mk]
  exact (contD (h i) |>.differentiable (by simp) 0).hasDerivAt

lemma Giving.tangent (hp : Giving p P 0) (ht : p 0 = X) (n : ℕ) :
    Giving (fun i => p i ^ (n + 1)) (((n + 1 : ℕ) : ℕ) • (P * X ^ n)) 0 := by
  induction n with
  | zero => simpa only [Nat.zero_add, pow_zero, one_smul, pow_one, mul_one] using hp
  | succ n ih =>
    obtain h := ih.prod hp
    simp only [ht] at h
    rw [show ((n + 1 + 1) : ℕ) • (P * X ^ (n + 1)) = (n + 1) • (P * X ^ n) * X + (X ^ (n + 1)) * P
        from ?_]
    swap
    · rw [smul_mul_assoc, add_smul, one_smul, pow_succ, mul_assoc]
      ring
    convert h using 1
    ext1 t
    exact pow_succ ..

lemma bend (v : Cn) (hp : Rooted P) (n : ℕ) :
    let g (i : ℕ) : ℂ := coeff n ((i + 1 : ℕ) • (P * X ^ i)) * coeff (i + 1) v;
    ∑ i ∈ Finset.range n, g i = coeff n (PowerSeries.derivative ℂ v * P) := by
  intro g
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j =>
      coeff i (PowerSeries.derivative ℂ v) * coeff j P),
    Finset.sum_range_succ]
  simp only [Nat.sub_self, hp, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hh := Finset.mem_range.mp hj
  let m := n - j
  have he : coeff n (P * X ^ j) = coeff m P := by
    rw [PowerSeries.coeff_mul_X_pow']
    simp [m, hh.le]
  unfold g
  rw [map_nsmul, he, PowerSeries.coeff_derivative]
  simp [m]
  ring

lemma Giving.post (k : Cn) (hp : Giving F P 0) (hs : Rooted P) (hv : ∀ i, Rooted (F i))
    (he : F 0 = X) : Giving (fun i => k.subst (F i)) (PowerSeries.derivative ℂ k * P) 0 := by
  intro j
  simp_rw [usePool (hv _),
    show Finset.Iic j = Finset.range (j + 1) from Finset.ext (fun i => by simp),
    Finset.sum_range_succ', cut, pow_zero]
  rw [← bend k hs]
  exact
    HasDerivAt.add_const _ (HasDerivAt.fun_sum (fun i _ => (Giving.tangent hp he i j).mul_const _))
end chain
section funds
variable {M : Booked (Ensure.deck G)} {F : MS_Data G M} {V : Store G} (P : Rose.Pick V)
  {W : Initialize G}
variable (hG : G.Simple) {A : Prescription (Ensure.deck G)} (hp : Installed W F A) (hh : Commuting A)

abbrev vRate (r : ℝ) :=
  transit P F r
omit hh hp hG

lemma tonicX : speed (transit P F) := fun n => Raha.transit_coin P F n
include hG hp hh

lemma tonic : speed (muFlow P F) := by
  have hw := ψ_aware P hG hp hh
  obtain he := awareχ P hG hp hh 0
  let f (p : ℝ) := PowerSeries.subst (χMS 0 P F) (transit P F p)
  have h : speed f := speed.reexpress (tonicX P) (speed.const _) (fun _ => he.root)
  exact speed.reexpress (speed.const (ψW P F)) h (fun t => ((flowAware P hG hp hh t).extend he).root)

lemma init : transit P F 0 = X := by
  unfold transit
  rw [neg_zero]
  exact (awareχ P hG hp hh 0).undo

lemma βη (s : ℝ) : Giving (transit P F) (PowerSeries.subst (transit P F s) (Beta (transit P F))) s := by
  intro i
  have he := Giving.pre (p := transit P F) (flowAware P hG hp hh s |>.root) (certBeta (tonicX P)) i
  simp_rw [(scale_law P hG hp hh s _).2] at he
  let g : ℝ → ℂ := fun v => coeff i (transit P F v)
  let f (v : ℝ) := v - s
  have hx : f s = 0 := sub_self _
  have hv : HasDerivAt f 1 s := (hasDerivAt_id' s).sub_const s
  have hs : (fun t => g (t + s)) ∘ f = g := funext fun t => congr_arg g (sub_add_cancel t s)
  have hL : HasDerivAt (fun t => g (t + s)) _ (f s) := hx.symm ▸ he
  have h := hL.scomp s hv
  rw [hs, one_smul] at h
  exact h

lemma β_seed : Rooted (Beta (transit P F)) ∧ coeff 1 (Beta (transit P F)) = 0 := by
  unfold Rooted Beta
  simp only [PowerSeries.coeff_mk]
  simp_rw [(flowAware P hG hp hh _).root, (flowAware P hG hp hh _).paid]
  simp

lemma identity_β :
    let f := ψW P F
    PowerSeries.subst f (Beta (muFlow P F)) = PowerSeries.derivative ℂ f * Beta (transit P F) := by
  intro f
  apply PowerSeries.ext
  intro n
  let p := transit P F
  refine
    (Giving.pre (p := muFlow P F) (ψ_aware P hG hp hh |>.root) (certBeta (tonic P hG hp hh)) n).unique
      ?_
  simp_rw [scaleMS_f P hG hp hh]
  exact
    Giving.post f (certBeta (tonicX P)) (β_seed P hG hp hh).1 (fun i => (flowAware P hG hp hh i).root)
      (init P hG hp hh) n
end funds
end YM.WilsonMS.Datum
