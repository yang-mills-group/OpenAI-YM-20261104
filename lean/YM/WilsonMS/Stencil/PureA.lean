import YM.WilsonMS.Stencil.Midpoint
/-!
# Proving `Fits` on the uncorrected dictionary

Match momentum jets of a given rank and reading size. Incorporate the exact
fits certificates in the construction of a portfolio (`LitBook`) which can
later use the literal MS endpoints on this basis.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Webs.Midpt
open Function Filter Finset Set MeasureTheory XSpace
open Lattice RG Maxwell Source Labels Maxwell.Free Wilson
open MS MS.Local MS.Local.Physical MS.Plane MS.Koszul MS.Theater MS.Tone
open MS.Menus MS.Land MS.Local.BV MS.Cylinder MS.Book MS.Native MS.Puff.Actors MS.Landau.Detect
open MS.Native.Sew MS.Native.Studio MS.Native.Wilsonian MS.Native.Chart MS.Native.Draft
  MS.Cylinder.Lab MS.Cylinder.Taylor
open Work Drops Tensor YM.Analysis G03
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {H : Source.Hol G} {p : Labels.Pol G} {d j h : ℕ} (A : Survey G H d)
local notation "E" => Edge Cover
local notation "U" => Lot G E
open MS.Tone.Frame MS.Lifting

abbrev priceKey (i : Labels.Key G) := fun x => (reader A (MvPolynomial.X i) (packetU A x)).re

lemma into_ink (i : Labels.Key G) (v : LightMode G QP) :
    run (Webs.symbol A (MvPolynomial.X i)) [v] =
      ∑ j : Webs.Wire A × Conn G,
        paywave v (knot (site A) j) * (↑(layer (priv j) (priceKey A i) 0) : ℂ) := by
  rw [symbol_X]
  change shade _ (Ferry _ _) _ = _
  rw [study]
  let F : Cyl (Webs.Wire A × Conn G) ℂ := region.symm (ink priv (priceKey A i))
  rw [deriv_lum (fun p x => paywave p (knot (site A) x)) v F
      (show Uses ((Finset.univ : Finset (Webs.Wire A × Conn G)) : Set _) F.val from
        (by simp [Uses.entire]))]
  apply Finset.sum_congr rfl
  intro j _
  rw [shade_nil]
  rfl

lemma planDeriv (p q : QP) (t : ℝ) :
    HasDerivAt (fun x : ℝ => bill (x • p) q)
      ((Complex.I * (Momentum.pairing p q : ℂ)) * bill (t • p) q) t := by
  let h := Momentum.pairing p q
  have hp (x : ℝ) : Momentum.pairing (x • p) q = x * h := by
    unfold h Momentum.pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (x * p i) * q i = _
    ring
  unfold bill
  simp_rw [hp]
  have he : HasDerivAt (fun x : ℝ => Complex.I * ((x * h : ℝ) : ℂ)) (Complex.I * h) t := by
    apply HasDerivAt.const_mul
    have ht : HasDerivAt (fun x : ℝ => x * h) h t := by simpa using (hasDerivAt_id' t).mul_const h
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ ht
  exact he.cexp.congr_deriv (mul_comm ..)

lemma billDeriv (p q : QP) (t : ℝ) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => bill (x • p) q) t =
      (Complex.I * (Momentum.pairing p q : ℂ)) ^ j * bill (t • p) q := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ',
      show deriv (fun x : ℝ => bill (x • p) q) = _ from funext fun i => (planDeriv p q i).deriv,
      iteratedDeriv_const_mul_field, ih, pow_succ']
    ring

lemma bill_read (p q : QP) (j : ℕ) :
    Plane.reading j (fun x : ℝ => bill (x • p) q) =
      hitϑ j * (↑(amount j * Momentum.pairing p q ^ j) : ℂ) := by
  rw [Plane.reading, billDeriv, zero_smul, pay0, Complex.real_smul]
  unfold hitϑ amount
  push_cast
  ring

private lemma single_axis (x : Axis) : fixF (Frame.z x) = (1 / 2 : ℝ) • basis x := by
  unfold Frame.z
  rw [map_smul]
  congr 1
  apply PiLp.ext
  intro i
  change ((step x i : ℤ) : ℝ) = _
  by_cases h : i = x <;> simp [*, Ne.symm]

lemma mid_pair (p : QP) (x : Cover) (a : Axis) :
    Momentum.pairing p (Tone.embed x + Frame.z a) = inner ℝ (fixF p) (station (x, a) (1 / 2)) := by
  let y := Tone.embed x + Frame.z a
  rw [show station (x, a) (1 / 2) = fixF y from ?_]
  swap
  · unfold y
    rw [map_add, single_axis]
    rfl
  change ∑ i, p i * y i = _
  apply Finset.sum_congr rfl
  intro i _
  change p i * y i = y i * p i
  ring
variable (i : Axis) (p : QP) (k : Conn G)

def shelf (v : LightMode G Cover) (t : ℝ) :=
  paywave (waveForm (t • p) i k) v

lemma supported (x : Webs.Wire A) (y : Conn G) :
    let v := knot (site A) (x, y);
    ContDiff ℝ ∞ (shelf i p k v) := by
  let X := knot (site A) (x, y)
  intro v
  change ContDiff ℝ ∞ (fun t : ℝ => paywave (waveForm (t • p) i k) (formAt (site A x).2 y _))
  simp_rw [please]
  unfold matchA
  split_ifs with a b <;>
    first
    | exact contDiff_const
    | exact Lifting.bankForm ..

lemma rank_wave (j : ℕ) (x : Webs.Wire A) (y : Conn G) :
    Plane.reading j (shelf i p k (knot (site A) (x, y))) =
      hitϑ j * (↑(projector (x, y) (lookPt (speak j i p (Theater.cl G k)) ∘ site A)) : ℂ) := by
  unfold shelf knot
  simp_rw [please]
  unfold matchA
  rw [projector_k]
  simp only [Function.comp_apply, lookPt, Midpt.value]
  by_cases he : i = (site A x).2
  swap
  · rw [trace_vanish i _ he]
    simp only [if_neg he]
    split <;> simp [Plane.reading]
  rw [← he, on_print]
  change _ = hitϑ j * (Complex.ofReal (((_ : ℝ) • Theater.cl G k) y))
  by_cases hy : y = k
  · subst y
    simp only [if_true]
    rw [bill_read, mid_pair]
    unfold Theater.cl
    simp only [PiLp.smul_apply, EuclideanSpace.single, PiLp.single_apply, ↓reduceIte, smul_eq_mul,
      mul_one]
    rw [he]
  simp only [if_neg hy]
  unfold Theater.cl
  simp [Plane.reading, hy]

lemma stageInk (u : Labels.Key G) (j : ℕ) :
    Plane.reading j (fun t : ℝ => run (Webs.symbol A (MvPolynomial.X u)) [waveForm (t • p) i k]) =
      hitϑ j * (evaluateL A u (lookPt (speak j i p (Theater.cl G k))) : ℂ) := by
  let e := priceKey A u
  let T := lookPt (speak j i p (Theater.cl G k))
  let L := T ∘ site A
  let f := fun v : Webs.Wire A × Conn G => shelf i p k (knot (site A) v)
  let P := fderiv ℝ e 0
  simp_rw [into_ink]
  change Plane.reading j (fun t => ∑ i, f i t * ↑(P (priv i))) = _
  have he (v : Webs.Wire A × Conn G) :
    Plane.reading j (fun t => f v t * ↑(P (priv v))) =
      (↑(P (priv v)) : ℂ) * (hitϑ j * ↑(projector v L)) := by
    rw [show (fun t => f v t * _) = _ from (funext fun t => mul_comm (f v t) _), read_const]
    exact congr_arg ((↑(P (priv v)) : ℂ) * ·) (rank_wave A i p k j v.1 v.2)
  rw [read_sum (f := fun (v : Webs.Wire A × Conn G) t => f v t * (↑(P (priv v)) : ℂ))
      (fun v _ => (supported A i p k v.1 v.2).mul contDiff_const)]
  simp_rw [he]
  rw [show evaluateL A u (lookPt _) = P L from (exposes A u T).symm]
  nth_rw 2 [← Native.frame L]
  rw [map_sum, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  simp_rw [smul_eq_mul]
  push_cast
  ring

lemma rank_fit (u : Labels.Key G) (hu : u.1 + 2 ≤ d) (i : Axis) (p : QP) (k : Conn G) :
    Rest (fun t : ℝ => run (Webs.symbol A (MvPolynomial.X u)) [waveForm (t • p) i k])
      (↑(u.1 + 1 : ℕ) : ℤ) (lamp u (waveForm p i k)) := by
  rcases u with ⟨u, v⟩
  constructor
  · simp_rw [into_ink]
    exact
      ContDiff.sum fun j _ => show ContDiff ℝ ∞ _ from (supported A i p k j.1 j.2).mul contDiff_const
  · intro h
    omega
  intro j hj
  rw [stageInk, ← sends A i p (Theater.cl G k) _ hu j (by omega)]
  split
  · rename_i h
    obtain rfl : j = u + 1 := by
      simp only at h
      omega
    rw [read_top A _ v hu]
    rfl
  rename_i h
  rw [read_void A _ hu _
      (by
        simp only at *
        omega),
    Complex.ofReal_zero, mul_zero]

lemma no_shapes (u : Labels.Key G) (a : MS.Landau.Branch G Axis) (p : QP)
    (he : ∀ i : Axis, a.1 ≠ Landau.gauge i) :
    Rest (fun t : ℝ => run (Webs.symbol A (MvPolynomial.X u)) [(a, t • p)])
      (generation u - Landau.wfield a) (lamp u (a, p)) := by
  have hp (p : QP) : run (Webs.symbol A (MvPolynomial.X u)) [(a, p)] = 0 := by
    rw [into_ink]
    apply Finset.sum_eq_zero
    intro j _
    have h : paywave (a, p) (knot (site A) j) = 0 :=
      Classical.byContradiction fun h =>
        he _ (congr_arg Prod.fst (in_light (a, p) (knot (site A) j) h))
    rw [h, zero_mul]
  simp_rw [hp]
  rw [show lamp u (a, p) = 0 from ?_]
  exact Rest.zero _
  rcases a with ⟨⟨_ | a, _ | _⟩, c⟩ <;>
    first
    | rfl
    | exact (he a rfl).elim

lemma first_fit (a : Labels.Key G) (h : a.1 + 2 ≤ d) :
    Fits (Webs.symbol A (MvPolynomial.X a)) (orbit G (MvPolynomial.X a)) 1 (generation a) false := by
  rw [cusp]
  apply Fits.rank1
  intro b p
  by_cases he : ∃ i, b.1 = Landau.gauge i
  swap
  · exact no_shapes A a b p fun j h => he ⟨j, h⟩
  rcases he with ⟨i, hi⟩
  rcases b with ⟨b, k⟩
  change b = Landau.gauge i at hi
  subst b
  have hf := rank_fit A _ h i p k
  convert hf using 1 <;> try rfl
  unfold generation
  change ((↑(a.fst + 2 : ℕ) : ℤ) - 1) = _
  omega

lemma total_fit (p : Labels.Pol G) (k : ℕ × ℕ) (hp : At p k) :
    k.1 ≤ d → Fits (Webs.symbol A p) (orbit G p) k.2 k.1 false := by
  refine axisI (fun k p => k.1 ≤ d → Fits (Webs.symbol A p) (orbit G p) k.2 k.1 false) hp ?_ ?_ ?_ ?_
  · intro c _
    rw [symbol_C, cus]
    let F := Fits.unit (G := G) (b := false)
    convert F.smul c using 1
    · apply Subtype.ext
      funext l
      cases l
      exact (mul_one c).symm
      exact (mul_zero c).symm
    · ext1 l
      cases l
      exact (mul_one c).symm
      exact (mul_zero c).symm
    · rfl
    rfl
  · intro j _
    rw [show Webs.symbol A 0 = 0 from
        add_left_cancel (a := Webs.symbol A 0) (b := Webs.symbol A 0) (c := 0)
          (by rw [← sum_part, add_zero, add_zero]),
      map_zero]
    exact Fits.zero _
  · intro u i f ht hh h
    change i.1 + 2 + u.1 ≤ d at h
    rw [product_X, bags]
    rw [Prod.fst_add, Prod.snd_add, Nat.cast_add]
    exact (first_fit A i (by omega)).take (hh (by omega)) (starts_X A i) (starts A (p := f) ht)
  intro x f g he hg hf hh H
  rw [sum_part, map_add]
  exact (hf H).add (hh H)

def portfolio (W : Initialize G) : LitBook (Ensure.deck G)
    where
  stamp d _ i := Webs.symbol (W.surveys d) (Theater.film (Ensure.deck G) i)
  levels _ _ _ := esteem _ (filmW ..)
  fit d v
    i := by
    rw [← lamp_here (h := d)]
    exact total_fit _ _ (d, v) (filmW (Ensure.deck G) i |>.2) le_rfl
end YM.WilsonMS.Webs.Midpt
