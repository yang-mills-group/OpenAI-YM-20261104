import YM.WilsonMS.Calibration.TurnTapes
/-!
# Within-grade rotations in label coordinates

Use real scalars. Keep the direction of leg flow ($θ$ opposite to actual
field action). Compatible across horizons. Need not orthogonalize the basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Bin
open Function Filter Set Finset MeasureTheory
open Lattice XSpace Maxwell Source Labels Free
open MS Plane Koszul Landau Wind Book Convolve Program Arts Native Wilsonian
open Menus Local.Physical High Knobs Detect Theater HBeam Trading BMenu Land Native.Orient
open Complex (I)
open scoped Topology ContDiff Interval Classical
variable {G : Gauge} {d r h : ℕ} (s : Signed)
local notation "B" => Ensure.deck G

abbrev BinI (G : Gauge) (d k : ℕ) :=
  (Ensure.deck G).BIndex (d : ℤ) k

abbrev position (a : Fin (d + 1)) (i : Fin (a.val + 1)) (x : BinI G a.val i.val) : Glyph B d :=
  ⟨a, i, x⟩

private lemma job {v : WickPol G} (hp : v ∈ IvSpace G d r) : reflectPol s.ortho v ∈ IvSpace G d r := by
  obtain ⟨x, rfl⟩ := hp
  let P : Labels.Label G d := ⟨x.val, Theater.limitH x.property.2, (cinema _ |>.mp x.property).2.1⟩
  let y := Labels.tensor s.ortho P
  have hv : y.val = Labels.rotated s.ortho x.val := rfl
  have ha : y.val ∈ Film0 G d r := (cinema _).mpr ⟨still _ x.property.2, y.property.2, ?_⟩
  swap
  · exact
      congr_arg (fun v : Labels.Label G d => v.val)
        (show realBar y = y from
          Eq.trans (Labels.real_turn _ _)
            (congr_arg (Labels.tensor s.ortho) (Subtype.ext (cinema _ |>.mp x.property |>.2.2))))
  exact ⟨⟨y.val, ha⟩, pulls_label P s.ortho⟩

private def movedR (s : Signed) (G : Gauge) (d r : ℕ) : Module.End ℝ (IvSpace G d r) :=
  (((reflectPol s.ortho).toLinearMap.restrictScalars ℝ).comp (IvSpace G d r).subtype).codRestrict
    (IvSpace G d r) (fun x => job s x.property)

private lemma actR (t : Signed) (v : IvSpace G d r) :
    movedR (s * t) G d r v = movedR s G d r (movedR t G d r v) := by
  apply Subtype.ext
  change reflectPol (s * t).ortho v.val = _
  rw [show (s * t).ortho = s.ortho * t.ortho from map_mul Signed.inclusionO ..]
  exact pol_mul ..

def indexR (s : Signed) (d k : ℕ) (i j : BinI G d k) : ℝ :=
  ((Indigo B d k).repr (movedR s G d k (Indigo B d k i))) j

lemma exactly (a : Fin (d + 1)) (b : Fin (a.val + 1)) (i : BinI G a.val b.val) :
    Labels.tensor s.ortho (data0 (position a b i)) =
      ∑ j, indexR s a.val b.val i j • data0 (position a b j) := by
  let R := movedR s G a.val b.val
  let X := Indigo B a.val b.val
  let p (j : BinI G _ _) := position a b j
  have he (i : BinI G a.val b.val) : (data0 (p i)).val = XSpace.On.lifting ((X i).val) := by
    rw [← letS B a b i]
    exact (Ensure.coincide G i).symm
  apply Subtype.ext
  change Labels.rotated s.ortho (data0 (p i)).val = _
  rw [he, ← XSpace.On.lift_signed]
  rw [show reflectPol s.ortho (X i).val = (R (X i)).val from rfl]
  conv_lhs => rw [← X.sum_repr (R (X i))];
  let K := XSpace.On.lifting (G := G)
  let W := K.toLinearMap.restrictScalars ℝ
  change W _ = _
  change W ↑(_ : IvSpace G a.val b.val) = ((Labels.localFields G a.val).subtype.restrictScalars ℝ) _
  let L := (IvSpace G a.val b.val).subtype
  change W (L _) = ((Labels.localFields G a.val).subtype.restrictScalars ℝ) _
  simp_rw [map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congr_arg ((indexR s a.val b.val i j) • ·) (he j).symm

lemma ingested (x : BinI G d r) (v : BinI G d r) (t : Signed) :
    indexR (s * t) d r x v = ∑ i, indexR t d r x i * indexR s d r i v := by
  let K := Indigo B d r
  let g (c : Signed) := movedR c G d r
  have ht : g (s * t) (K x) = g s (∑ j, indexR t d r x j • K j) :=
    Eq.trans (actR s t _) (congr_arg _ (K.sum_repr _ |>.symm))
  change K.repr _ v = _
  rw [ht]
  simp_rw [map_sum, Finsupp.finsetSum_apply, map_smul]
  rfl

lemma lead1 (i j : BinI G d r) : indexR 1 d r i j = if i = j then 1 else 0 := by
  let K := Indigo B d r
  change K.repr (movedR 1 G d r _) j = _
  rw [show movedR 1 _ _ _ (K i) = K i from ?_, K.repr_self, Finsupp.single_apply]
  apply Subtype.ext
  change reflectPol (Signed.inclusionO 1) _ = _
  rw [map_one, pol_one]
  rfl
section full

def lines (s : Signed) (x : Glyph B d) (i : Glyph B d) : ℝ :=
  ∑ t : BinI G x.size x.grade,
    if position x.fst x.snd.fst t = i then indexR s x.size x.grade x.snd.snd t else 0

lemma common (a : Fin (d + 1)) (b : Fin (a.val + 1)) (x : BinI G a.val b.val)
    (y : BinI G a.val b.val) : lines s (position a b x) (position a b y) = indexR s a.val b.val x y := by
  let f (t : BinI G a.val b.val) := position a b t
  unfold lines
  rw [sum_eq_single y]
  exact if_pos rfl
  · intro i hi he
    exact if_neg (fun h => he ((by simpa [f, position] using (show f i = f y from h))))
  exact fun h => (h (mem_univ _)).elim

lemma bins (x i : Glyph B d) (hp : lines s x i ≠ 0) : x.size = i.size ∧ x.grade = i.grade := by
  by_contra he
  apply hp
  apply Finset.sum_eq_zero
  intro j hj
  refine if_neg fun h => ?_
  rw [← h] at he
  exact he ⟨rfl, rfl⟩

variable {E : Type} [AddCommMonoid E]

lemma extracted (a : Fin (d + 1)) (b : Fin (a.val + 1)) (F : Glyph B d → E)
    (hp : ∀ i, F i ≠ 0 → a.val = i.size ∧ b.val = i.grade) :
    ∑ i, F i = ∑ i : BinI G a.val b.val, F (position a b i) := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · rw [Fintype.sum_sigma, sum_eq_single b]
    · intro i _ hi
      exact
        Finset.sum_eq_zero fun j _ =>
          Classical.byContradiction fun h => hi (Fin.ext (hp _ h |>.2.symm))
    simp
  · intro i _ hi
    exact
      Finset.sum_eq_zero
        (fun j _ => Classical.byContradiction fun h => hi (Fin.ext (hp _ h |>.1.symm)))
  simp

lemma lines_mul (v p : Glyph B d) (t : Signed) : lines (s * t) v p = ∑ i, lines t v i * lines s i p := by
  rcases v with ⟨a, b, v⟩
  rcases p with ⟨j, k, p⟩
  by_cases he : a = j ∧ HEq b k
  · rcases he with ⟨rfl, h⟩
    obtain rfl : b = k := eq_of_heq h
    rw [extracted a b _ (fun i h => bins t _ _ (left_ne_zero_of_mul h)),
      show lines _ _ _ = _ from common (s * t) a b v p, ingested s v p t]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congr_arg₂ (· * ·) (Eq.symm (common t a b v i)) (Eq.symm (common s a b i p))
  have h : ¬(a.val = j.val ∧ b.val = k.val) := by
    rintro ⟨hy, hK⟩
    obtain rfl : a = j := Fin.ext hy
    exact he ⟨rfl, heq_of_eq (Fin.ext hK)⟩
  rw [show lines (s * t) ⟨a, b, v⟩ ⟨j, k, p⟩ = 0 from
      Classical.byContradiction fun hL => h (bins (s * t) _ _ hL)]
  symm
  exact
    Finset.sum_eq_zero fun i _ =>
      Classical.byContradiction fun H =>
        let hp := bins t _ _ (left_ne_zero_of_mul H);
        let hx := bins s _ _ (right_ne_zero_of_mul H);
        h ⟨hp.1.trans hx.1, hp.2.trans hx.2⟩

lemma lines_id (i j : Glyph B d) : lines 1 i j = if i = j then 1 else 0 := by
  rcases i with ⟨a, b, i⟩
  rcases j with ⟨k, t, j⟩
  by_cases he : a = k ∧ HEq b t
  · rcases he with ⟨rfl, h⟩
    obtain rfl : b = t := eq_of_heq h
    rw [show lines 1 _ _ = _ from common 1 a b i j, lead1]
    simp
  have h :
    ¬((position a b i).size = (position k t j).size ∧
        (position a b i).grade = (position k t j).grade) := by
    rintro ⟨hy, hz⟩
    obtain rfl : a = k := Fin.ext hy
    exact he ⟨rfl, heq_of_eq (Fin.ext hz)⟩
  rw [if_neg
      (fun H =>
        h
          (by
            refine
              ⟨congr_arg (fun i : Glyph B _ => i.size) H,
                congr_arg (fun i : Glyph B _ => i.grade) H⟩))]
  exact Classical.byContradiction fun he => h (bins 1 _ _ he)

lemma preamble_act (W : XSpace.Initialize G) (p : Team) (i : Glyph B d) (x : ℝ) (k : ℕ) :
    pose s (preambleW W p i x k) = ∑ j, (lines s i j : ℝ) • preambleW W p j x k := by
  rcases i with ⟨a, b, i⟩
  rw [extracted a b _ (fun j h => bins s _ j (left_ne_zero_of_smul h)), ← tab W p x (position a b i),
    veil_turn, exactly]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show lines _ _ _ = _ from common s a b i j, map_smul, ← tab]
  rfl
end full
section plaid
variable {V : Type} [AddCommMonoid V]

abbrev beta (s : Signed) (x y : Plaid B d) : ℝ :=
  lines s (Land.read x) (Land.read y)

lemma beta_c (a : Fin (d + 1)) (i j : BinI G d a.val) :
    beta s ⟨a, i⟩ (⟨a, j⟩ : Plaid B d) = indexR s d a.val i j :=
  common ..

lemma passes (x y : Plaid B d) (h : beta s x y ≠ 0) : x.fst = y.fst :=
  Fin.ext (bins s _ _ h |>.2)

lemma extract_p (F : Plaid B d → V) (a : Fin (d + 1)) (hp : ∀ i, F i ≠ 0 → a = i.fst) :
    ∑ i, F i = ∑ i : BinI G d a.val, F ⟨a, i⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hi
    apply Finset.sum_eq_zero
    intro j _
    exact Classical.byContradiction fun h => hi (hp _ h |>.symm)
  simp

lemma beta_mul (t : Signed) (x y : Plaid B d) : beta (s * t) x y = ∑ i, beta t x i * beta s i y := by
  rcases x with ⟨a, x⟩
  rw [extract_p _ a (fun i h => passes t _ _ (left_ne_zero_of_mul h))]
  unfold beta
  rw [lines_mul]
  exact extracted ⟨d, Nat.lt_succ_self d⟩ a _ (fun i h => bins t _ _ (left_ne_zero_of_mul h))

lemma beta_one (x y : Plaid B d) : beta 1 x y = if x = y then 1 else 0 := by
  unfold beta
  simp only [lines_id, show Land.read x = Land.read y ↔ x = y from (Ensure.read_inj ..).eq_iff]

def labelK (v : Plaid B d) : Labels.Label G d :=
  data0 (Land.read v)

lemma paper (v : Plaid B d) :
    Labels.tensor s.ortho (labelK v) = ∑ i : Plaid B d, beta s v i • labelK i := by
  rcases v with ⟨a, b⟩
  rw [extract_p _ a (fun i h => passes s _ _ (left_ne_zero_of_smul h)),
    show Labels.tensor _ (labelK (G := G) ⟨a, b⟩) = _ from exactly s ⟨d, Nat.lt_succ_self d⟩ a b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta_c]
  rfl

open Mach Motif Literal

lemma box_unique {X Y : Literal.Box (Mob G)} (h : ∀ z, Literal.value _ z X = Literal.value _ z Y) :
    X = Y := by
  apply sub_eq_zero.mp
  ext1 i
  funext m l
  exact valuedZ (X - Y) (Garment.Wave.slice l) (fun z => by rw [map_sub, h, sub_self, map_zero]) i

lemma row_chart (v : Plaid B d) :
    Boom 0 (rotateMob s⁻¹ G) ((JRad.book G).optics d v) =
      ∑ i : Plaid B d, (beta s v i : ℂ) • (JRad.book G).optics d i := by
  apply box_unique
  intro z
  have H := JRad.optic G
  simp_rw [Literal.linear_v, map_sum, map_smul, JRad.Book_formula]
  rw [show rotateMob s⁻¹ G _ = _ from congr_fun (JRad.signedK (ΕData B (Land.read v)) s⁻¹) z]
  simp_rw [show (s⁻¹).ortho = s.ortho⁻¹ from map_inv Signed.inclusionO s]
  let X := (JRad.optic G).restrictScalars ℝ
  change X ((Labels.tensor s.ortho (labelK v)).val) z = _
  rw [paper]
  let P := (Labels.localFields G d).subtype.restrictScalars ℝ
  change X (P _) z = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  rfl
open Dock Emit Train Outlook
variable (T : MS_Data G (JRad.book G))

lemma rota (x : Plaid B d) :
    Trading.record s⁻¹ G (Archive d (T.marks d x)) =
      ∑ i : Plaid B d, (beta s x i : ℂ) • Archive d (T.marks d i) := by
  let F := T.marks d
  let X := (JRad.book G).optics d
  let Y := ∑ i : Plaid B d, (beta s x i : ℂ) • F i
  let D := Boom 0 (rotateMob s⁻¹ G) (X x)
  let C := Emit.gloss (Literal.linear (Mob G) D)
  have hk := rotate_comet s⁻¹ T.bulkOK (T.markOK d x)
  let ca := moveM s⁻¹ G ∘ (F x)
  let y := ∑ i : Plaid B d, (beta s x i : ℂ) • T.poles d i
  have hp : comet d 0 T.bulk C ca (moveK s⁻¹ G ∘ T.poles d x) := by
    convert hk using 1
    funext w z n l
    unfold C Emit.gloss
    unfold D
    rw [Literal.whole]
    rfl
  have ht : comet d 0 T.bulk C Y y := by
    have hV : C = ∑ i : Plaid B d, (beta s x i : ℂ) • Emit.gloss (Literal.linear (Mob G) (X i)) := by
      rw [show C = Emit.gloss (Literal.linear _ D) from rfl, show D = _ from row_chart s x]
      funext y z
      simp only [Emit.gloss, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
      rfl
    rw [hV]
    exact sum_comet Finset.univ _ _ _ (fun i _ => smul_comet (T.markOK d i) _ (by simp))
  obtain ⟨HX, hc⟩ := unique_M hp ht (fun _ _ => EventuallyEq.rfl)
  funext n w
  rw [show Trading.record s⁻¹ _ _ n w = Outlook.four d (ca n) w from
      four_rot s⁻¹ (gang (T.markOK d x n) |>.dost) w,
    four_pact (gang (hp n) |>.dost) (gang (ht n) |>.dost) (hc n) w]
  unfold Y F
  simp_rw [Finset.sum_apply, Pi.smul_apply]
  rw [four_sum _ _ (fun i hi => Stay_scale (gang (T.markOK d i n) |>.dost) _), Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [four_smul (gang (T.markOK d i n) |>.dost)]
  rfl
end plaid
end YM.WilsonMS.Bin
