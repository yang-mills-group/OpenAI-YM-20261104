import YM.WilsonMS.Stencil.Curves
import YM.Work.G05.Taylor
/-!
# Comparing derivatives through a fixed horizon

The stencil proof uses several variables. Do not infer a moving-parameter
statement by naive 1-variable extraction with the second argument fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.TaylorRules
open Function Filter Set MeasureTheory
open Analysis Tensor
open scoped Topology ContDiff BigOperators Classical
variable {E X F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : E} {x : X} {k n : ℕ}

structure Agree (n : ℕ) (p : E) (f g : E → F) : Prop where
  smooth : ContDiffAt ℝ (↑n) f p
  smooth' : ContDiffAt ℝ (↑n) g p
  same : ∀ k ≤ n, iteratedFDeriv ℝ k f p = iteratedFDeriv ℝ k g p

namespace Agree
variable {f g h : E → F}

lemma refl (h : ContDiffAt ℝ (↑n) f p) : Agree n p f f :=
  ⟨h, h, fun _ _ => rfl⟩

lemma symm (e : Agree n p f g) : Agree n p g f :=
  ⟨e.smooth', e.smooth, fun k h => (e.same k h).symm⟩

lemma trans (e : Agree n p f g) (he : Agree n p g h) : Agree n p f h :=
  ⟨e.smooth, he.smooth', fun k hx => (e.same k hx).trans (he.same k hx)⟩

lemma lower (e : Agree n p f g) (h : k ≤ n) : Agree k p f g :=
  ⟨e.smooth.of_le (Nat.cast_le.mpr h), e.smooth'.of_le (Nat.cast_le.mpr h), fun _ hh =>
    e.same _ (hh.trans h)⟩

lemma value (e : Agree n p f g) : f p = g p := by
  have he := e.same 0 (Nat.zero_le _)
  rw [← iteratedFDeriv_zero_apply (f := f) (x := p) (𝕜 := ℝ) (m := (0 : Fin 0 → E)), ←
    iteratedFDeriv_zero_apply (𝕜 := ℝ) (m := (0 : Fin 0 → E)) (f := g), he]

lemma of_event (e : f =ᶠ[𝓝 p] g) (h : ContDiffAt ℝ (↑n) f p) : Agree n p f g :=
  ⟨h, h.congr_of_eventuallyEq e.symm, fun k _ => (e.iteratedFDeriv ℝ k).eq_of_nhds⟩

lemma comp {u v : F → X} (e : Agree n p f g) (he : Agree n (g p) u v) : Agree n p (u ∘ f) (v ∘ g) :=
  let ht : ContDiffAt ℝ (↑n) u (f p) := e.value.symm ▸ he.smooth
  ⟨ht.comp _ e.smooth, he.smooth'.comp _ e.smooth',
    Work.G05.jets_comp e.smooth e.smooth' ht he.smooth' e.value e.same he.same⟩

lemma apply_smooth (e : Agree n p f g) {u : F → X} (he : ContDiffAt ℝ (↑n) u (g p)) :
    Agree n p (u ∘ f) (u ∘ g) :=
  e.comp (refl he)

lemma pi_jet {ι : Type} [Fintype ι] {U V : E → (ι → F)}
    (he : ∀ i, Agree n p (fun x => U x i) (fun x => V x i)) : Agree n p U V := by
  have hu : ContDiffAt ℝ (↑n) U p := contDiffAt_pi.mpr fun i => (he i).smooth
  have hv : ContDiffAt ℝ (↑n) V p := contDiffAt_pi.mpr fun i => (he i).smooth'
  refine ⟨hu, hv, fun k hk => ?_⟩
  ext r i
  let L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i
  have ht := (he i).same k hk
  change iteratedFDeriv ℝ k (L ∘ U) p = iteratedFDeriv ℝ k (L ∘ V) p at ht
  rw [L.iteratedFDeriv_comp_left hu (Nat.cast_le.mpr hk),
    L.iteratedFDeriv_comp_left hv (Nat.cast_le.mpr hk)] at ht
  exact congr_arg (fun T : Tensor.T E F k => T r) ht

lemma pair {u v : E → X} (e : Agree n p f g) (he : Agree n p u v) :
    Agree n p (fun x => (f x, u x)) (fun x => (g x, v x)) := by
  refine ⟨e.smooth.prodMk he.smooth, e.smooth'.prodMk he.smooth', fun k hk => ?_⟩
  rw [iteratedFDeriv_prodMk e.smooth he.smooth (Nat.cast_le.mpr hk),
    iteratedFDeriv_prodMk e.smooth' he.smooth' (Nat.cast_le.mpr hk), e.same k hk, he.same k hk]

lemma add {u v : E → F} (e : Agree n p f g) (he : Agree n p u v) : Agree n p (f + u) (g + v) :=
  (e.pair he).apply_smooth (u := fun x : F × F => x.1 + x.2) (by fun_prop)

lemma smul_var {u v : E → ℝ} (e : Agree n p f g) (he : Agree n p u v) :
    Agree n p (fun x => u x • f x) (fun x => v x • g x) :=
  (e.pair he).apply_smooth (u := fun x : F × ℝ => x.2 • x.1) (by fun_prop)

lemma mul {R : Type} [NormedRing R] [NormedAlgebra ℝ R] {f g u v : E → R} (e : Agree n p f g)
    (he : Agree n p u v) : Agree n p (fun x => f x * u x) (fun x => g x * v x) :=
  (e.pair he).apply_smooth (u := fun x : R × R => x.1 * x.2) (by fun_prop)
section curve
variable {U V : ℝ → F} {t : ℝ}

lemma line (h : ContDiffAt ℝ (↑n) U t) (hh : ContDiffAt ℝ (↑n) V t)
    (he : ∀ k ≤ n, iteratedDeriv k U t = iteratedDeriv k V t) : Agree n t U V := by
  refine ⟨h, hh, fun k hk => ?_⟩
  apply ContinuousMultilinearMap.ext
  intro s
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    he k hk]

lemma along_line (e : Agree n t U V) (h : k ≤ n) : iteratedDeriv k U t = iteratedDeriv k V t :=
  congr_arg (fun V : Tensor.T ℝ F k => V 1) (e.same k h)
end curve
end Agree

section mixed
variable {f g : E × X → F}

lemma partial_first (h : ContDiffAt ℝ (↑n) f (p, x)) (u : Fin n → E) :
    iteratedFDeriv ℝ n f (p, x) (fun i => (u i, 0)) = iteratedFDeriv ℝ n (fun s => f (s, x)) p u := by
  induction n generalizing f p x with
  | zero => simp
  | succ n ih =>
    let U := u 0
    let r := Fin.tail u
    have hu : D U (fun i : E => f (i, x)) =ᶠ[𝓝 p] fun i => D (U, (0 : X)) f (i, x) := by
      filter_upwards [((continuous_id.prodMk (continuous_const (y := x))).continuousAt (x :=
              p)).tendsto.eventually
          (h.eventually (by simp))] with
        i hi
      let L := ContinuousLinearMap.inl ℝ E X
      have he : HasFDerivAt (fun i : E => (i, x)) L i :=
        (hasFDerivAt_id i).prodMk (hasFDerivAt_const x i)
      exact
        congr_arg (fun v : E →L[ℝ] F => v U)
          (((show ContDiffAt ℝ (↑(n + 1 : ℕ)) f (i, x) from hi).differentiableAt
                  (by simp)).hasFDerivAt.comp
              i he).fderiv
    have hv :
      Fin.cons (U, (0 : X)) (fun i => (r i, (0 : X))) = fun j : Fin (n + 1) => (u j, (0 : X)) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [U, r, Fin.tail]
    rw [← hv, cons_inner h,
      ih
        (dSmooth h _
          (by
            push_cast
            rfl))]
    nth_rw 1 [← show Fin.cons U r = u from Fin.cons_self_tail u]
    rw [cons_inner (f := fun i => f (i, x)) (h.comp (f := fun i => (i, x)) _ (by fun_prop)),
      (hu.iteratedFDeriv ℝ n).eq_of_nhds]

lemma cross_once (h : ContDiffAt ℝ (↑(n + 1 : ℕ)) f (p, x)) (s : Fin n → E) (u : X) :
    D u (fun x : X => iteratedFDeriv ℝ n (fun t : E => f (t, x)) p s) x =
      iteratedFDeriv ℝ n (fun t : E => D ((0 : E), u) f (t, x)) p s := by
  let V := fun i : Fin n => (s i, (0 : X))
  have he : iteratedFDeriv ℝ (n + 1) f (p, x) (Fin.cons ((0 : E), u) V) = _ :=
    (cons_inner h _ V).trans
      (partial_first (p := p) (x := x) (n := n)
        (dSmooth h _
          (by
            push_cast
            rfl))
        s)
  rw [← he, cons_jet h]
  let g (x : E × X) := iteratedFDeriv ℝ n f x V
  have hg : DifferentiableAt ℝ g (p, x) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ => E × X) F V).differentiableAt.comp (f :=
      iteratedFDeriv ℝ n f) _ (h.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr n.lt_succ_self))
  have hh :
    (fun x : X => g (p, x)) =ᶠ[𝓝 x] (fun x : X => iteratedFDeriv ℝ n (fun t : E => f (t, x)) p s) := by
    have hf : ContDiffAt ℝ (↑n) f (p, x) := h.of_le (Nat.cast_le.mpr (by omega))
    filter_upwards [(((continuous_const (y := p)).prodMk continuous_id).continuousAt (x :=
            x)).tendsto.eventually
        (hf.eventually (by simp))] with
      x hx
    exact partial_first hx s
  have hv : HasFDerivAt (fun x : X => (p, x)) (ContinuousLinearMap.inr ℝ E X) x :=
    (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  exact
    congr_arg (fun L : X →L[ℝ] F => L u)
      ((hg.hasFDerivAt.comp x hv).congr_of_eventuallyEq hh.symm).fderiv

/-- Fix the vertical argument `p`. Pointwise equality through n along those
fibres *for every parameter in a neighborhood* implies equality of full jets. -/
theorem family (hf : ContDiffAt ℝ (↑n) f (p, x)) (hg : ContDiffAt ℝ (↑n) g (p, x))
    (hx :
      ∀ᶠ y in 𝓝 x,
        ∀ k ≤ n,
          iteratedFDeriv ℝ k (fun p => f (p, y)) p = iteratedFDeriv ℝ k (fun p => g (p, y)) p) :
    Agree n (p, x) f g := by
  refine ⟨hf, hg, fun k hk => ?_⟩
  induction k generalizing n p x f g with
  | zero =>
    ext1 s
    have hq := congr_arg (fun U : Tensor.T E F 0 => U 0) (hx.self_of_nhds 0 (by omega))
    simpa using hq
  | succ k ih =>
    ext1 s
    have ht : ContDiffAt ℝ (↑(k + 1 : ℕ)) f (p, x) := hf.of_le (Nat.cast_le.mpr hk)
    have hu : ContDiffAt ℝ (↑(k + 1 : ℕ)) g (p, x) := hg.of_le (Nat.cast_le.mpr hk)
    rw [← Fin.cons_self_tail s]
    let a := (s 0).1
    let b := (s 0).2
    let U := (a, (0 : X))
    let V := ((0 : E), b)
    have split (F' : E × X → F) :
      iteratedFDeriv ℝ (k + 1) F' (p, x) (Fin.cons (s 0) (Fin.tail s)) =
        iteratedFDeriv ℝ (k + 1) F' (p, x) (Fin.cons U (Fin.tail s)) +
          iteratedFDeriv ℝ (k + 1) F' (p, x) (Fin.cons V (Fin.tail s)) := by
      rw [show s 0 = U + V by simp [U, V, a, b]]
      let W := (iteratedFDeriv ℝ (k + 1) F' (p, x)).curryLeft
      exact congr_arg (fun T : Tensor.T (E × X) F k => T (Fin.tail s)) (map_add W U V)
    rw [split f, split g]
    simp only [cons_inner ht, cons_inner hu]
    apply congr_arg₂ (· + ·)
    · suffices he : iteratedFDeriv ℝ k (D U f) (p, x) = iteratedFDeriv ℝ k (D U g) (p, x) by rw [he]
      refine
        ih (n := k)
          (dSmooth ht U
            (by
              push_cast
              rfl))
          (dSmooth hu U
            (by
              push_cast
              rfl))
          ?_ le_rfl
      filter_upwards [hx,
        ((continuous_const.prodMk continuous_id).continuousAt (x := x)).tendsto.eventually
          (ht.eventually (by simp)),
        ((continuous_const.prodMk continuous_id).continuousAt (x := x)).tendsto.eventually
          (hu.eventually (by simp))] with
        y HY Hf Hg i hi
      ext1 s
      have he (f : E × X → F) (h : ContDiffAt ℝ (↑(k + 1 : ℕ)) f (p, y)) :
        iteratedFDeriv ℝ i (fun t => D U f (t, y)) p s =
          iteratedFDeriv ℝ (i + 1) (fun t => f (t, y)) p (Fin.cons a s) := by
        have hh : ContDiffAt ℝ (↑(i + 1 : ℕ)) f (p, y) := h.of_le (Nat.cast_le.mpr (by omega))
        rw [← partial_first hh, ←
          partial_first (p := p) (x := y) (n := i)
            (dSmooth hh _
              (by
                push_cast
                rfl)),
          ← cons_inner hh]
        congr 1
        funext t
        refine Fin.cases ?_ (fun _ => ?_) t <;> simp [U]
      rw [he f Hf, he g Hg, HY (i + 1) (by omega)]
    suffices he : iteratedFDeriv ℝ k (D V f) (p, x) = iteratedFDeriv ℝ k (D V g) (p, x) by rw [he]
    obtain ⟨B, hB, hO, hK⟩ := mem_nhds_iff.mp hx
    refine
      ih (n := k)
        (dSmooth ht V
          (by
            push_cast
            rfl))
        (dSmooth hu V
          (by
            push_cast
            rfl))
        ?_ le_rfl
    filter_upwards [hO.mem_nhds hK,
      ((continuous_const.prodMk continuous_id).continuousAt (x := x)).tendsto.eventually
        (ht.eventually (by simp)),
      ((continuous_const.prodMk continuous_id).continuousAt (x := x)).tendsto.eventually
        (hu.eventually (by simp))] with
      y HY Hf Hg i hi
    ext1 s
    have ht' : ContDiffAt ℝ (↑(k + 1 : ℕ)) f (p, y) := Hf
    have hu' : ContDiffAt ℝ (↑(k + 1 : ℕ)) g (p, y) := Hg
    dsimp only [V]
    rw [← cross_once (ht'.of_le (Nat.cast_le.mpr (show i + 1 ≤ k + 1 by omega))), ←
      cross_once (hu'.of_le (Nat.cast_le.mpr (show i + 1 ≤ k + 1 by omega)))]
    unfold D
    have he :
      (fun x : X => iteratedFDeriv ℝ i (fun t : E => f (t, x)) p s) =ᶠ[𝓝 y]
        (fun x : X => iteratedFDeriv ℝ i (fun t : E => g (t, x)) p s) :=
      (show ∀ᶠ z in 𝓝 y, z ∈ B from hO.mem_nhds HY).mono fun z (hv : z ∈ B) =>
        congr_arg (fun t : Tensor.T E F i => t s) (hB hv i (by omega))
    rw [he.fderiv_eq]
end mixed
end YM.WilsonMS.TaylorRules
