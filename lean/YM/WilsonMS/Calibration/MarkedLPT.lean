import YM.WilsonMS.Calibration.Replot
/-!
# Pay on those Wilson columns, including marked prefixes
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open Function Filter Set Finset MeasureTheory XSpace
open Lattice Maxwell Source Labels Maxwell.Free Wilson
open MS MS.Plane MS.High MS.Native MS.Native.Wilsonian MS.Native.Studio
open MS.Menus MS.Local.Physical MS.Land MS.Book MS.Book.Convolve MS.Book.Program
open Cylinder Lab MS.Koszul MS.Lifting MS.Theater Tone Landau.Detect
open MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.SplitP MS.Puff.Mom Swirl Swirl.Near Fleet
open Rescaled Webs Corrected
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {d l r : ℕ} (W : XSpace.Initialize G) (φ : Team) (x : ℝ) {c t : XSpace.Period}
  {n : ℕ}
local notation "B" => Ensure.deck G

section dictionary
variable {H : Hol G} (A : Survey G H d) {p : Labels.Pol G}
variable (T : t.Tree) (w v : Cover) (hp : p ∈ Film0 G l r)
local notation "N" => t.side

abbrev ordinaryR (p : Labels.Pol G) (w : Cover) : Obs (P := t) G := fun X =>
  (reader A p (expandAt (wrap t.side w) X)).re

lemma read_eq (X : Obs (P := t) G) (a : Site N) (i : Config G N) :
    translateO G X a i = X (i ∘ translateE a) :=
  rfl

lemma expand_here (p : Labels.Pol G) :
    translateO G (Complex.re ∘ ORead A N p) (wrap N w) = ordinaryR A p w := by
  ext1 U
  unfold ordinaryR Rescaled.translateO ORead
  simp only [Function.comp_apply]
  apply congr_arg (fun x => (reader A p x).re)
  ext1 i
  unfold expandAt
  simp only [Function.comp_apply, add_zero]
  exact congr_arg U (Prod.ext (add_comm ..) rfl)
include hp

lemma offeredR : Offered (P := t) G (ordinaryR A p w) r := by
  rw [← expand_here]
  apply pays G (F := Webs.symbol A p)
  · rw [Webs.sym_real A ((cinema ..).mp hp |>.2.2), Webs.paymentR]
    rfl
  · exact Webs.inkVia A p
  · exact Webs.starts A ((Theater.cinema ..).mp hp).1
  intro a U
  rw [show Native.Chart.siteGauge _ a U = Lattice.gauge (a⁻¹) U from ?_]
  unfold Webs.ORead
  simp_rw [Function.comp_apply, expandAt_gauge]
  exact congr_arg Complex.re (Webs.color_inv A ((cinema ..).mp hp).2.1 _ _)
  ext1 i
  simp [MS.Native.Chart.siteGauge, MS.Native.Chart.drive, MS.Native.Chart.endRail, Lattice.gauge]

lemma x_normalization :
    Root.bareMark T G (Quo.asTree G (ordinaryR A p w)) r = Bare.raw T A (wrap N w) p := by
  have he (A B₀ : Bare.Series T G) (h : PowerSeries.X ^ r * A = PowerSeries.X ^ r * B₀) : A = B₀ :=
    PowerSeries.X_pow_mul_inj.mp h
  refine he _ _ ?_
  rw [mul_comm (PowerSeries.X ^ r), Rescaled.laurent T G (offeredR A w hp),
    XSpace.Bare.coefficient_weight T A (wrap N w)]
  · apply congr_arg
    funext y
    rw [show Bare.labelFunction T A (wrap N w) p y = reader A p (expandAt (wrap N w) (T.links y)) from
        rfl]
    change (↑(tested_function T G (ordinaryR A p w) y) : ℂ) = _
    rw [show tested_function T G (ordinaryR A p w) = (ordinaryR A p w) ∘ T.links from ?_]
    exact (is_real A ((cinema p |>.mp hp).2.2) _).symm
    funext i
    unfold tested_function
    rw [Function.comp_apply, Function.comp_apply, Root.plant_exp]
    rfl
  intro i hi
  have ht := (nodeId _ _ |>.mp hp.2) (MvPolynomial.mem_support_iff.mp hi)
  rw [weight_slot] at ht
  exact congr_arg Prod.snd ht.symm

lemma received_pair :
    Correspond T G φ x
      (promote (Mark_T G N w v) (wobble G (Stripped φ) x (levels r (Webs.symbol A p))))
      (Coupling.composeS (Program.shift φ x) (Bare.raw T A (wrap N (w + v)) p)) := by
  rw [← x_normalization A T (w + v) hp, strip_wobble]
  change Correspond T G φ x _ (litMark T G φ x _ r)
  refine translate_pair T G φ x _ _ (offeredR A (w + v) hp) ?_
  rw [← expand_here]
  refine translate_body G _ _ ?_ (inkVia A p)
  rw [Webs.sym_real A ((cinema ..).mp hp).2.2, paymentR]
  rfl
end dictionary
section physics
variable (P : Period) (T : P.Tree) (w v : Cover)
local notation "N" => P.side
variable (a : Glyph (Ensure.deck G) d)
local notation "y" => wrap N (w + v)

abbrev marker (a : Glyph B d) (z : Cover) :=
  Bare.column T (W.surveys a.size) (wrap N z) (data0 a)

lemma parse (a : Glyph B d) :
    marker W P T a (w + v) =
      Bare.raw T (W.surveys a.size) y (Theater.ΕData B a) +
        ∑ j : (more a), Bare.raw T (W.surveys a.size) y (further W a j).val := by
  let S := W.surveys a.size
  let X (q : Labels.Label G a.size) := Bare.raw T S y q.val
  unfold marker
  rw [Bare.column_formula, labels_split S (data0 a) (dataHere a)]
  unfold Bare.raw
  rw [Submodule.coe_add, AddSubmonoidClass.coe_finsetSum, map_add, map_sum]
  simp_rw [AddSubmonoidClass.coe_finsetSum, map_sum]
  rw [Fintype.sum_prod_type]
  congr! 1
  change (∑ i ∈ Finset.range (a.size + 1), ∑ j ∈ Finset.range a.grade, _) = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

lemma comp_add {R : Type} [CommRing R] [Algebra ℂ R] (c : Cn) (hp : Rooted c) (p q : PowerSeries R) :
    Coupling.composeS c (p + q) = Coupling.composeS c p + Coupling.composeS c q :=
  PowerSeries.subst_add
    (PowerSeries.HasSubst.of_constantCoeff_zero (Coupling.const_coupling (S := R) hp)) p q

lemma comp_sum {R J : Type} [CommRing R] [Algebra ℂ R] (V : Finset J) (c : Cn) (hp : Rooted c)
    (p : J → PowerSeries R) :
    Coupling.composeS c (∑ i ∈ V, p i) = ∑ i ∈ V, Coupling.composeS c (p i) := by
  unfold Coupling.composeS
  simp_rw [←
    PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (Coupling.const_coupling (S := R) hp)),
    map_sum]
variable {P T}

lemma sends :
    Correspond T G φ x (promote (Mark_T G N w v) (preambleW W (Stripped φ) a x))
      (Coupling.composeS (Program.shift φ x) (marker W P T a (w + v))) := by
  rw [preambleW, vertices, map_add, map_sum, map_add, map_sum, parse, comp_add _ (share ..),
    comp_sum _ _ (share φ x)]
  exact
    (received_pair φ x (W.surveys a.size) T w v (Theater.filmBasic B a)).add
      (Correspond.sum _
        (fun i _ => received_pair φ x _ T w v (piece_lit _ _ (realG a) i.1.val i.2.val)))

variable (P T)

def markArray (w : Cover) (A : Acts (Ensure.deck G) d) : Bare.Series T G :=
  ∑ g : Glyph B d,
    XSpace.Bare.scalar T (wavesP A x g) * Coupling.composeS (Program.shift φ x) (marker W P T g w)

/-- This binds the real Wilson-measure coefficients to the `rentW` actors. -/
lemma aligned (A : Acts (Ensure.deck G) d) :
    Correspond T G φ x (promote (Mark_T G N w v) (rentW W (Stripped φ) A x))
      (markArray W φ x P T (w + v) A) := by
  rw [stages, map_sum]
  apply Correspond.sum
  intro i _
  obtain h := Correspond.scale (wavesP A x i) (sends (P := P) (T := T) W φ x w v i)
  refine Eq.mp ?_ h
  rw [← scaleLinear]
  rw [Rescaled.priced,
    show Coupling.read (wavesP A x i) = fun n => oil A i n x from
      funext fun n => PowerSeries.coeff_mk ..]

end physics
end YM.WilsonMS.BMenu
