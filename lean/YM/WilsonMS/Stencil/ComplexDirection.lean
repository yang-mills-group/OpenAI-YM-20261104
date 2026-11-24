import YM.WilsonMS.Stencil.PotentialWord
/-!
# Plane test support. Real multidifferentials on two channels.

Extending the test at *each momentum direction* by multilinearity—not
assuming complex holonomies. Koszul evaluation for words of connection type.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Extract
open Function Filter Set MeasureTheory
open Analysis Tensor TPath Source Paths TaylorRules MS
open Complex (I)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] {ι : Type} {p : X} {u v : ι → E}

def delta (i : ι) (u v : ι → E) (f : E → ℂ) : E → ℂ :=
  D (u i) f + I • D (v i) f

def scans (u v : ι → E) (f : E → ℂ) (z : List ι) : E → ℂ :=
  match z with
  | [] => f
  | i :: l => scans u v (delta i u v f) l

abbrev Smooth {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : E → F) :=
  ContDiff ℝ ∞ X
variable {f g : E → ℂ}

lemma band (h : Smooth f) (i : ι) : Smooth (delta i u v f) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    (dSmooth (h.contDiffAt (x := x)) _ (by simp)).add
      (ContDiffAt.const_smul I (dSmooth (h.contDiffAt (x := x)) (v i) (by simp)))

lemma profile (h : Smooth f) (l : List ι) : Smooth (scans u v f l) := by
  induction l generalizing f with
  | nil => exact h
  | cons i l ih => exact ih (band h _)

lemma sc_zero (l : List ι) : scans u v 0 l = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [scans, show delta i u v 0 = 0 from funext fun x => by simp [delta, D], ih]

lemma sum2 (h : Smooth f) (hh : Smooth g) (l : List ι) :
    scans u v (f + g) l = scans u v f l + scans u v g l := by
  induction l generalizing f g with
  | nil => rfl
  | cons i l ih =>
    simp only [scans]
    rw [show delta i u v (f + g) = delta i u v f + delta i u v g from ?_]
    exact ih (band h i) (band hh i)
    unfold delta Analysis.D
    have he (x : E) : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
      fderiv_add (h.differentiable (by simp) _) (hh.differentiable (by simp) _)
    ext1 x
    simp only [Pi.add_apply, Pi.smul_apply, he, _root_.add_apply, smul_add]
    abel

lemma scale_s (h : Smooth f) (c : ℂ) (l : List ι) : scans u v (c • f) l = c • scans u v f l := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [scans, scans, show delta i u v (c • f) = c • delta i u v f from ?_]
    exact ih (band h _)
    unfold delta Analysis.D
    funext x
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [fderiv_const_smul (h.differentiable (by simp) x), smul_add]
    simp [mul_left_comm I]

lemma sc_minus (h : Smooth f) (hh : Smooth g) (l : List ι) :
    scans u v (f - g) l = scans u v f l - scans u v g l := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g, sum2 (g := (-1 : ℂ) • g) h (hh.const_smul (-1 : ℂ)),
    scale_s hh, neg_one_smul, sub_eq_add_neg]

lemma sc_sum {α : Type} {F : α → E → ℂ} {S : Finset α} (h : ∀ i ∈ S, Smooth (F i)) (l : List ι) :
    scans u v (∑ i ∈ S, F i) l = ∑ i ∈ S, scans u v (F i) l := by
  induction S using Finset.induction with
  | empty => simp [sc_zero]
  | insert b s he ih =>
    have ht (i) (hi : i ∈ s) := h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert he, sum2 (h b (Finset.mem_insert_self ..)) ?_, ih ht, Finset.sum_insert he]
    rw [show ∑ i ∈ s, F i = (fun x => ∑ i ∈ s, F i x) from
        Eq.symm (funext fun x => Eq.symm (Finset.sum_apply ..))]
    exact ContDiff.sum ht

lemma dprod (h : Smooth f) (hh : Smooth g) (i : ι) :
    delta i u v (f * g) = delta i u v f * g + f * delta i u v g := by
  funext x
  simp only [delta, D, Pi.mul_apply, Pi.smul_apply, Pi.add_apply]
  have he :=
    ((h.differentiable (by simp) x).hasFDerivAt.mul'
        (hh.differentiable (by simp) x).hasFDerivAt).fderiv
  rw [he]
  change
    (f x * (fderiv ℝ g x) (u i) + (fderiv ℝ f x) (u i) * g x) +
        I * (f x * (fderiv ℝ g x) (v i) + (fderiv ℝ f x) (v i) * g x) =
      _
  simp only [smul_eq_mul]
  ring

lemma const (c : ℂ) (l : List ι) : scans u v (fun _ => c) l 0 = Koszul.coin c l := by
  cases l with
  | nil => rfl
  | cons i l =>
    rw [scans, show delta i u v (fun _ => c) = 0 from funext fun x => by simp [delta, D], sc_zero]
    rfl

lemma sc_times {K : Type} (σ : Koszul.Sector K) (w : ι → K) (hw : ∀ i, σ (w i) = false)
    (F H : Koszul.Raw K ℂ) (h : Smooth f) (hh : Smooth g)
    (he : ∀ l : List ι, scans u v f l 0 = F (l.map w))
    (ht : ∀ l : List ι, scans u v g l 0 = H (l.map w)) (l : List ι) :
    scans u v (f * g) l 0 = Koszul.product σ F H (l.map w) := by
  induction l generalizing F H f g with
  | nil =>
    change f 0 * g 0 = Koszul.times σ F H []
    rw [Koszul.times_nil, show f 0 = _ from he [], show g 0 = _ from ht []]
    rfl
  | cons i l ih =>
    rw [scans, dprod h hh,
      sum2 (f := delta i u v f * g) (g := f * delta i u v g) ((band h i).mul hh) (h.mul (band hh i)),
      List.map_cons, Koszul.D_eval _ (Koszul.product σ F H), Koszul.D_product, hw, Koszul.sign_id,
      Pi.add_apply, Pi.add_apply]
    exact
      congr_arg₂ (· + ·) (ih (Koszul.D (w i) F) H (band h i) hh (fun l => he (i :: l)) ht)
        (ih F (Koszul.D (w i) H) h (band hh i) he (fun l => ht (i :: l)))

section commutation
variable {f g : X × E → ℂ}

abbrev delPar (u v : ι → E) (i : ι) (f : X × E → ℂ) : X × E → ℂ := fun x =>
  delta i u v (fun t => f (x.1, t)) x.2

lemma delPar_s (h : Smooth f) (i : ι) : Smooth (delPar u v i f) := by
  rw [show delPar u v i f = delta i (fun j => (0, u j)) (fun j => ((0 : X), v j)) f from ?_]
  exact band h i
  funext x
  have hx (z : E) : D z (fun y : E => f (x.1, y)) x.2 = D ((0 : X), z) f x := by
    have hv : HasFDerivAt (fun y : E => (x.1, y)) (ContinuousLinearMap.inr ℝ X E) x.2 :=
      (hasFDerivAt_const x.1 _).prodMk (hasFDerivAt_id _)
    exact
      DFunLike.congr_fun
        ((show DifferentiableAt ℝ f (x.1, x.2) from h.differentiable (by simp) x).hasFDerivAt.comp
            (f := fun y : E => (x.1, y)) x.2 hv).fderiv
        z
  simp [delPar, delta, hx]

def scPar (u v : ι → E) (w : List ι) (f : X × E → ℂ) (x : X × E) :=
  scans u v (fun t => f (x.1, t)) w x.2

lemma scPar_s (h : Smooth f) (w : List ι) : Smooth (scPar u v w f) := by
  induction w generalizing f with
  | nil => exact h
  | cons i l ih =>
    change Smooth (scPar u v l (delPar u v i f))
    exact ih (delPar_s h i)

lemma iterated (h : Smooth f) (n : ℕ) (s : Fin n → X) (l : List ι) (x : X) (y : E) :
    iteratedFDeriv ℝ n (fun z : X => scPar u v l f (z, y)) x s =
      scans u v (fun y : E => iteratedFDeriv ℝ n (fun z : X => f (z, y)) x s) l y := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [show
        (fun z : X => scPar u v (i :: l) f (z, y)) =
          (fun z : X => scPar u v l (delPar u v i f) (z, y))
        from rfl,
      ih (delPar_s h i), scans]
    congr 2
    funext e
    let g (z : X) (b : E) := D b (fun w => f (z, w)) e
    have ht (b : E) : Smooth (fun z : X => g z b) := by
      let P : Unit → E := fun _ => 0
      let K : Unit → E := fun _ => b
      let Q (z : X) : X × E := (z, e)
      have hp := (delPar_s (u := K) (v := P) h ()).comp (f := Q) (contDiff_id.prodMk contDiff_const)
      rw [show (fun z => g z b) = delPar K P () f ∘ Q from ?_]
      exact hp
      funext x
      change _ = _ + I * ((fderiv ℝ _ _) (0 : E))
      rw [map_zero, mul_zero, add_zero]
    let V (y : E) := iteratedFDeriv ℝ n (fun z : X => f (z, y)) x s
    have hv (b : E) : iteratedFDeriv ℝ n (fun z : X => g z b) x s = D b V e := by
      have he (z : X) : g z b = D ((0 : X), b) f (z, e) := by
        let L : E →L[ℝ] X × E := ContinuousLinearMap.inr ℝ X E
        have hh : HasFDerivAt (fun y : E => (z, y)) L e :=
          (hasFDerivAt_const ..).prodMk (hasFDerivAt_id _)
        exact DFunLike.congr_fun ((h.differentiable (by simp) (z, e)).hasFDerivAt.comp _ hh).fderiv b
      rw [funext he]
      exact (cross_once (contDiffAt_infty.mp h.contDiffAt _) s b).symm
    rw [show (fun z : X => delPar u v i f (z, e)) = (fun z => g z (u i)) + I • (fun z => g z (v i))
        from rfl,
      iteratedFDeriv_add_apply (g := I • (fun z => g z (v i)))
        (contDiffAt_infty.mp (ht (u i) |>.contDiffAt) _)
        (contDiffAt_infty.mp ((ht (v i)).const_smul I |>.contDiffAt) _),
      iteratedFDeriv_const_smul_apply (contDiffAt_infty.mp (ht (v i) |>.contDiffAt) _),
      _root_.add_apply]
    rw [_root_.smul_apply, hv, hv]
    rfl

lemma attends (h : Smooth f) (hh : Smooth g) (n : ℕ)
    (H : ∀ y, Agree n p (fun x => f (x, y)) (fun x => g (x, y))) (w : List ι) (y : E) :
    Agree n p (fun x => scPar u v w f (x, y)) (fun x => scPar u v w g (x, y)) := by
  refine
    ⟨contDiffAt_infty.mp (((scPar_s h w).comp (contDiff_id.prodMk contDiff_const)).contDiffAt) n,
      contDiffAt_infty.mp (((scPar_s hh w).comp (contDiff_id.prodMk contDiff_const)).contDiffAt) n,
      fun k hk => ?_⟩
  ext1 s
  rw [iterated h, iterated hh]
  congr 2
  funext z
  rw [(H z).same k hk]
end commutation
end YM.WilsonMS.Extract
