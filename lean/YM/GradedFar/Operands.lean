import Mathlib.LinearAlgebra.Multilinear.Curry
import YM.FVA2.O.Enh.Twigs
import YM.GradedFar.Columns
import YM.GradedFar.Crop
import YM.GradedFar.Slots
/-!
# Exact Far installation, with mixed field caps

Everything here is on `Sec`, with the `up` inclusions. The stationary correlation family used
is an actual `A : Scale.Arenas G`; in the application, `Scale.Measure.outlook`. Similarly `F`
is instantiated by the `GroupS.gaugeN` of the *same* prescription. The argument to
those Frames is `η : ℝ` and the power series is in t. No extra coupling subst or inverse of F,
no conversion of a Near field.

See `fullSeries`, `replacementSeries`. Fields converted **before** cropping, indeed before
promoting to a common measurement horizon. Real mixed caps. Common horizon for measurement can
be any allowed `l`, same in both uses. These definitions make `x,y` always shapes in their
respective units; use `η = -log T`. All uses at this `T` thus ask `A` for Far positions
**`T • y`**. Extension by zero off `conf` (bounds will apply actually in `conf`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
abbrev Through (l : ℕ) (d : Fin n → ℕ) := ∀ i, d i ≤ l
abbrev AppointedH140Through (l : ℕ) (d : Fin n → ℕ) := ∀ i, d i ≤ l
abbrev Output (h : ℕ) := fun _ : Fin 1 => h
abbrev AppointedH140Inputs (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Sec G (d i)
abbrev Both (G : Gauge) (d : Fin n → ℕ) (e : Fin m → ℕ) :=
  MultilinearMap ℂ (fun i => Sec G (d i)) (MultilinearMap ℂ (fun i => Sec G (e i)) ℂ)

section operators
variable (A : Arenas G) (F : ℝ → Frames G) (η : ℝ)
variable (hd : Through l d) (he : Through l e) (z : Points (n+m))
    (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e)

/-- K(η) = D_{exp(-η)} times the running conversion. -/
def conversion (η : ℝ) : Frames G := fun d => PowerSeries.C (Level.Dial d η) * F η d

lemma coeff_conversion (i d : ℕ) (a : Sec G d) :
    coeff i (conversion F η d) a = Level.Dial d η (coeff i (F η d) a) := by
  rw [conversion, coeff_C_mul]; rfl

abbrev raised (hd : Through l d) (u : Inputs G d) : Tags G l n := fun i => up (hd i) (u i)

/-- Unconverted full at positions `z`; the domain is mixed-cap. -/
def rawCoeff (k : ℕ) : Both G d e :=
  if hz : z ∈ conf (n+m) then
    (MultilinearMap.compLinearMapₗ (fun i => up (G:=G) (he i))).compMultilinearMap
      (((A l _ ⟨z,hz⟩ k).domDomCongr finSumFinEquiv.symm).currySum.compLinearMap
        (fun i => up (G:=G) (hd i)))
  else 0

lemma rawCoeff_apply (k : ℕ) (hz : z ∈ conf (n+m)) :
    rawCoeff A hd he z k u v = A l _ ⟨z,hz⟩ k (Fin.append (raised hd u) (raised he v)) := by
  rw [rawCoeff, dif_pos hz]
  apply congrArg (A l _ ⟨z,hz⟩ k)
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma rawCoeff_off (k : ℕ) (hz : z ∉ conf (n+m)) : rawCoeff A hd he z k u v = 0 := by
  rw [rawCoeff, dif_neg hz]; rfl

/-- Formal insertion on just the Far fields, general Far conversion parameter W (at the fixed η).
`tally` is the allocation of order k; see `Dframe.Constants.admits`. -/
def withFar (W : Frames G) (hd : Through l d) (he : Through l e) (z : Points (n+m))
    (k : ℕ) : Both G d e :=
  ∑ a ∈ Normalize.tally k m,
    (MultilinearMap.compLinearMapₗ (fun i => coeff (a (some i)) (W (e i)))).compMultilinearMap
      (rawCoeff A hd he z (a none))

lemma withFar_apply (W : Frames G) (hd : Through l d) (he : Through l e) (z : Points (n+m))
    (u : Inputs G d) (v : Inputs G e) (k : ℕ) :
    withFar A W hd he z k u v = ∑ a ∈ Normalize.tally k m,
      rawCoeff A hd he z (a none) u (fun i => coeff (a (some i)) (W (e i)) (v i)) := by
  simp only [withFar, sum_apply]; rfl

def fullSeries : PowerSeries ℂ :=
  PowerSeries.mk fun k => withFar A (conversion F η) hd he (forest x (squeeze η y)) k u v

/-- Near replaced by a single field through h at the origin. -/
abbrev replacementSeries (hh : h ≤ l) (he : Through l e) (y : Points m)
    (a : Sec G h) (v : Inputs G e) :=
  fullSeries A F η (d:=Output h) (fun _ => hh) he 0 y (fun _ => a) v

lemma fullSeries_at_T (t : ℝ) (ht : 0 < t) (hz : forest x (t • y) ∈ conf (n+m)) (k : ℕ) :
    coeff k (fullSeries A F (-Real.log t) hd he x y u v) = ∑ a ∈ Normalize.tally k m,
      A l _ ⟨forest x (t • y), hz⟩ (a none) (Fin.append (raised hd u)
        (raised he fun i => coeff (a (some i)) (conversion F (-Real.log t) (e i)) (v i))) := by
  rw [fullSeries, coeff_mk, withFar_apply, squeeze, neg_neg, Real.exp_log ht]
  simp_rw [rawCoeff_apply _ _ _ _ _ _ _ hz]
end operators

abbrev InCaps (d : Fin n → ℕ) (u : Scan G n) := ∀ i, heft (u i) ≤ d i
abbrev loadScan (p : Scan G n) (v : InCaps d p) : Inputs G d := fun i => cap (p i) (v i)
lemma stillInCaps {p : Scan G n} (a : LivesP p) (h : InCaps d p) : InCaps d (decode p a) := h

lemma rawCoeff_on_scan (A : Arenas G) (H : Regular A) (hd : Through l d) (he : Through l e)
    (U : Scan G n) (V : Scan G m) (hu : InCaps d U) (hv : InCaps e V) (z : Points (n+m)) (k : ℕ) :
    rawCoeff A hd he z k (loadScan U hu) (loadScan V hv) = coeff k (install A _ z (Fin.append U V)) := by
  by_cases hz : z ∈ conf (n+m)
  · let W := Fin.append U V
    have hw : Guarded W l := by
      intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [show W (Fin.castAdd m j) = _ from Fin.append_left U V j]; exact (hu j).trans (hd j)
      rw [show W (Fin.natAdd n j) = _ from Fin.append_right U V j]; exact (hv j).trans (he j)
    rw [caring W hw H hz, rawCoeff_apply _ _ _ _ _ _ _ hz, O.Score.test,
      Reg.Point.story, coeff_mk]
    apply congrArg (A l _ ⟨z,hz⟩ k); funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]; unfold tape W; simp only [Fin.append_left]; rfl
    simp only [Fin.append_right]; unfold tape W; simp only [Fin.append_right]; rfl
  rw [rawCoeff_off _ _ _ _ _ _ _ hz, install, dif_neg hz, map_zero]

/-! The sums over homogeneous labels, with the per-slot caps requested.
Use the max norm in this basis for the frame-label balls (or pay larger fixed radii).
`Box` spelled out as the simultaneous bounds, so no global norm instances required. -/
abbrev Picks (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Toon G (d i)
abbrev indexScan (p : Picks G d) : Scan G n := fun i => Dframe.flash (p i)
abbrev boundedByCaps (p : Picks G d) : InCaps d (indexScan p) := fun i => size_le (p i)
abbrev basisWord (p : Picks G d) := loadScan (indexScan p) (boundedByCaps p)

lemma basis_letter (p : Picks G d) (i : Fin n) : basisWord p i = theory (p i) := rfl

def multipliers (u : Inputs G d) (p : Picks G d) := ∏ i, coord (p i) (u i)

def Box (u : Inputs G d) (L : ℝ) : Prop := ∀ i, ∀ q : Toon G (d i), ‖coord q (u i)‖ ≤ L

lemma multipliers_le {L : ℝ} (_hp : 0 ≤ L) (u : Inputs G d) (p : Picks G d) (h : Box u L) :
    ‖multipliers u p‖ ≤ L^n := by
  unfold multipliers; rw [norm_prod]; refine (Finset.prod_le_prod (fun i _ => norm_nonneg _)
    (fun i _ => h i (p i))).trans_eq ?_
  simp

/-- The given cap-wise basis, truly expanding in *every* slot. -/
theorem basis_sum {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : MultilinearMap ℂ (fun i => Sec G (d i)) E) (u : Inputs G d) :
    f u = ∑ p : Picks G d, multipliers u p • f (basisWord p) := by
  have hu i : (∑ a : Toon G (d i), coord a (u i) • theory a) = u i := all_sig (u i)
  have hx := f.map_sum (fun i a => coord a (u i) • theory a)
  simp_rw [hu] at hx; rw [hx]
  exact Finset.sum_congr rfl fun p _ => f.map_smul_univ _ (basisWord p)

-- useful selection identity
lemma basis_delta (a b : Picks G d) :
    multipliers (basisWord a) b = if a=b then 1 else 0 := by
  unfold multipliers; simp_rw [basis_letter, pivotδ]
  split_ifs with h
  · subst b; simp
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end YM.FVA2.GradedFar

/-!
# The two formal rows with running graded Far fields, and the OPE vector

Keep the caps on each slot. Say explicitly how to build these series (basis form), and
prove it buys the actual predictions, coefficientwise with each Far slot of the kernel
on its full series of column arguments.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m ℓ h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
def combo (u : Inputs G d) (c : Choices G d) : ℂ := ∏ i, coord (c i) (u i)
def installedInputs (hL : ∀ i, d i ≤ ℓ) (u : Inputs G d) : Tags G ℓ n :=
  fun i => up (hL i) (u i)
def basisInputs (c : Choices G d) : Inputs G d := fun i => theory (c i)
lemma basis_spelling (F : MultilinearMap ℂ (fun i => Sec G (d i)) ℂ) (v : Inputs G d) :
    F v = ∑ c : Choices G d, combo v c * F (basisInputs c) := by
  have ht := F.map_sum (fun i (c : Toon G (d i)) => coord c (v i) • theory c)
  simp_rw [reconstructed] at ht
  rw [ht]
  exact Finset.sum_congr rfl fun i _ => F.map_smul_univ _ (basisInputs i)

/-- Expand just the Far slots of a given `Point` (already on their `up` inclusions). -/
lemma expand_far (F : Point G ℓ (n+m)) (u : Tags G ℓ n) (v : Inputs G e) (he : ∀ i, e i ≤ ℓ) :
    F (Fin.append u (installedInputs he v)) = ∑ c : Choices G e,
      combo v c * F (Fin.append u (installedInputs he (basisInputs c))) :=
  basis_spelling ((freezeNear F u).compLinearMap (fun i => up (he i))) v
lemma expand_near (F : Point G ℓ (n+m)) (u : Inputs G d) (v : Tags G ℓ m) (hd : ∀ i, d i ≤ ℓ) :
    F (Fin.append (installedInputs hd u) v) = ∑ a : Choices G d,
      combo u a * F (Fin.append (installedInputs hd (basisInputs a)) v) :=
  basis_spelling ((freezeFar F v).compLinearMap (fun i => up (hd i))) u

section
-- algebraic multilinearity; applies for every pair of shapes in the domain
variable (V : Arenas G) {x : Points n} {Y : Points m}

lemma append_guarded (a : Choices G d) (c : Choices G e) (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ) :
    Guarded (Fin.append (roll a) (roll c)) ℓ := by
  intro i
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact (Dframe.size_le (a i)).trans (hd i)
  | right j => rw [Fin.append_right]; exact (Dframe.size_le (c j)).trans (he j)

lemma coeff_party (r : Regular V) (a : Choices G d) (c : Choices G e)
    (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ) (hg : forest x Y ∈ conf (n+m)) (j : ℕ) :
    coeff j (party (install V) x Y (roll a) (roll c)) = V ℓ _ ⟨forest x Y,hg⟩ j
      (Fin.append (installedInputs hd (basisInputs a)) (installedInputs he (basisInputs c))) := by
  rw [party, caring _ (append_guarded a c hd he) r hg]
  unfold O.Score.test Reg.Point.story; rw [coeff_mk]
  apply congrArg _
  funext i
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; unfold tape; simp only [Fin.append_left]; rfl
  | right i => rw [Fin.append_right]; unfold tape; simp only [Fin.append_right]; rfl

end

section apply
variable (P : Album G) (x : Points n) (Y : Points m) (u : Inputs G d) (X : Columns G e)
/-- Extend the graded kernel at `(x,Y)` by multilinearity, over scalar series, in the actual
far columns `X`, not truncated/evaluated legs. Near legs are constant. -/
def applyFar : PowerSeries ℂ := ∑ a : Choices G d, C (combo u a) *
  ∑ c : Choices G e, factors c X * party P x Y (roll a) (roll c)

def emitted (X : Columns G e) (D : Days m) : Inputs G e := fun i => X i (D (some i))

/-- Actual convolution equation for both rows. The number of Far slots
may even be zero. No data dependence of K on the formal coupling beyond
its power series. -/
theorem coeff_applyFar (V : Arenas G) (r : Regular V) (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ)
    (hc : forest x Y ∈ conf (n+m)) (j : ℕ) :
    coeff j (applyFar (install V) x Y u X) = ∑ D ∈ Normalize.tally j m,
      V ℓ _ ⟨forest x Y,hc⟩ (D none)
        (Fin.append (installedInputs hd u) (installedInputs he (emitted X D))) := by
  let F k := V ℓ _ ⟨forest x Y,hc⟩ k
  let val k (a : Choices G d) (v : Inputs G e) :=
    F k (Fin.append (installedInputs hd (basisInputs a)) (installedInputs he v))
  have co (c : Choices G e) (w : PowerSeries ℂ) : coeff j (factors c X * w) =
      ∑ D ∈ Normalize.tally j m, combo (emitted X D) c * coeff (D none) w := by
    rw [factors, Constants.admits]; unfold combo mode; simp_rw [coeff_mk]; rfl
  have part (a : Choices G d) : coeff j (∑ c : Choices G e, factors c X *
        party (install V) x Y (roll a) (roll c)) =
      ∑ D ∈ Normalize.tally j m, val (D none) a (emitted X D) := by
    simp_rw [map_sum,co,coeff_party V r _ _ hd he hc]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun D _ =>
      (expand_far (F _) (installedInputs hd (basisInputs a)) (emitted X D) he).symm
  unfold applyFar; rw [map_sum]; simp_rw [coeff_C_mul, part, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun D _ =>
    (expand_near (F _) u (installedInputs he (emitted X D)) hd).symm

/-- Basis center through the given horizon, exactly same `(Y,X)`. -/
def center (P : Album G) (Y : Points m) (X : Columns G e) (q : Toon G h) : PowerSeries ℂ :=
  ∑ c : Choices G e, factors c X * lonelyG P Y (flash q) (roll c)
/-- All linear combinations of these basis centers. -/
def responses (a : Sec G h) : PowerSeries ℂ :=
  ∑ q : Toon G h, C (coord q a) * center P Y X q

lemma responses_eq (a : Sec G h) : responses P Y X a =
    applyFar (d:=fun _ => h) P (0:Points 1) Y (fun _ => a) X := by
  unfold responses applyFar
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Toon G h)).symm]
  unfold combo center; simp only [Fin.prod_univ_one]; rfl


end apply
section sphere
variable (N : WilsonPrescription G)
  (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e)
/-- Yˣ. Arguments with center-origin convention. `s` in these two definitions is
*log T*. (The power-series variable is coupling.) -/
def Yx (s : ℝ) : PowerSeries ℂ := applyFar (ordinary N) x (squeeze (-s) y) u (exterior N T (-s) v)
/-- Dˣ on an actual cap-h label. -/
def Dx (s : ℝ) (a : Sec G h) : PowerSeries ℂ := responses (ordinary N) (squeeze (-s) y)
  (exterior N T (-s) v) a
/-- The genuine FarCoefficients, extended multilinearly in the input. -/
def seriesComponent (q : Q G) : PowerSeries ℂ := ∑ a : Choices G d, C (combo u a) *
  FarCoefficients (book N) (roll a) x q
/-- Vector in precisely the output sector, orderwise. -/
def vector (h : ℕ) (i : ℕ) : Sec G h := ∑ q : Toon G h, coeff i (seriesComponent N x u (flash q)) • theory q

def cActual (h p : ℕ) (t : ℝ) : Sec G h := ∑ i ∈ Finset.range (p+1), (t:ℂ)^i • vector N x u h i

lemma vector_coord (q : Toon G h) (i : ℕ) : coord q (vector N x u h i) = coeff i
    (seriesComponent N x u (flash q)) := by
  unfold vector
  simp_rw [map_sum, _root_.map_smul,pivotδ]; simp
lemma coord_actual (q : Toon G h) (t : ℝ) (p : ℕ) : coord q (cActual N x u h p t) = crop p t
    (seriesComponent N x u (flash q)) := by
  unfold cActual
  rw [crop_eq]
  rw [map_sum]; simp_rw [_root_.map_smul,vector_coord,smul_eq_mul]
end sphere
end
end YM.FVA2.GradedFar
