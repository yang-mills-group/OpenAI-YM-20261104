import YM.WilsonMS.Regulator.FrameD
/-!
# Match the prescribed point samples, before passing to Profile limits

Be careful about placing the symbols in the actual *translated* origin. Sum only
at inserted positions (even n=0 considered), retain ∫ over center with mass one
for these physical reports. Expand coupling into Spec by coefficient algebra,
never as a value at a coupling. This is the finite linear-algebra step needed
*before* using the $T$ estimates. For UV path still have to estimate the actual terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Fiscal
open Function Filter Set Finset MeasureTheory Real
open Lattice XSpace Normalize Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Plane MS.Menus MS.Land MS.Book MS.Book.Convolve MS.Book.Program Theater
open Bin BMenu Rider Rescaled
open Complex (I)
open PowerSeries (coeff mk constantCoeff)
open scoped Topology ContDiff Interval BigOperators Classical
variable {G : Gauge} {d h n j k : ℕ} (A : Prescription (Ensure.deck G)) (W : XSpace.Initialize G)
local notation "B" => Ensure.deck G
variable (p : XSpace.Mesh) (x η : ℝ)
section eval

local notation "T" => W.tree p.p
local notation "Sp" => XSpace.Bare.Series T G

def site (d : ℕ) (y : p.Sites) : Sec G d →ₗ[ℂ] XSpace.Bare.Series (W.tree p.p) G :=
  ∑ a : Fin (d + 1), (W.atSite p a.val y) ∘ₗ part d a.val

lemma atGrade (h : k ≤ d) (v : On.Grade G k) (y : p.Sites) :
    site W p d y (en h v) = W.atSite p k y v := by
  unfold site
  rw [LinearMap.sum_apply, Finset.sum_eq_single (⟨k, by omega⟩ : Fin (d + 1))]
  · rw [LinearMap.comp_apply, part_same]
  · intro b _ hb
    rw [LinearMap.comp_apply,
      part_other v
        (by
          intro hv
          exact hb (Fin.ext hv)),
      map_zero]
  simp

def point (d : ℕ) (v : Fin n → p.Sites) :
    MultilinearMap ℂ (fun _ : Fin n => Sec G d) (PowerSeries ℂ) :=
  (Bare.normalized (W.tree p.p) G).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℂ (Fin n) Sp).compLinearMap fun i => site W p d (v i))

lemma pointN (y : Fin n → p.Sites) (x : Fin n → Sec G d) :
    point W p d y x = Bare.normalized (W.tree p.p) _ (∏ i, site W p d (y i) (x i)) :=
  rfl

lemma pointGrade (K : Fin n → Fin (d + 1)) (y : Fin n → p.Sites) (x : ∀ i, On.Grade G (K i)) :
    in_grade (point W p d y) K x = W.atTuple p (fun i => (K i).val) y x := by
  rw [Normalize.in_grade, pointN]
  simp_rw [atGrade]
  rfl

def write (p : XSpace.Mesh) (y : Fin n → p.Sites) (t : Test n) : ℂ :=
  (p.spacing : ℂ) ^ (4 * n) * p.smear (Lattice.lift ∘ y) t

lemma total (t : Test n) (a : Fin n → Sec G d) (j : ℕ) :
    batch W p d j n t a = ∑ y : Fin n → p.Sites, write p y t * coeff j (point W p d y a) := by
  rw [calls (batch W p d j n t) a]
  have hp (r : Fin n → Fin (d + 1)) :
    in_grade (batch W p d j n t) r (fun i => part d _ (a i)) =
      ∑ y : Fin n → p.Sites,
        write p y t * coeff j (in_grade (point W p d y) r (fun i => part d _ (a i))) := by
    simp_rw [Normalize.indicated, pointGrade]
    rw [Initialize.report_formula, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, Finset.mul_sum, write, mul_assoc]
  change ∑ r : Fin n → Fin (d + 1), in_grade _ r _ = _
  simp_rw [hp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [calls (point W p d y), map_sum, Finset.mul_sum]
local notation "Ξ" => Program.shift A.team x

lemma shifted (r : Cn) (hp : Rooted r) (t : Test n) (a : Fin n → Sec G d) (j : ℕ) :
    substitute (P := Prediction G d) r (batch W p d) j n t a =
      ∑ y : Fin n → p.Sites, write p y t * coeff j (Coupling.composeS r (point W p d y a)) := by
  rw [rules, Finset.sum_apply, LinearMap.sum_apply, _root_.sum_apply]
  simp_rw [Pi.smul_apply, LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul, total, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [show coeff j _ = _ from congr_fun (Coupling.explicit hp (point W p d y a)).symm j, rules,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..

lemma space_at (hp : p.spacing = exp (-η)) (u : Glyph B d) (y : Cover) :
    site W p d (wrap p.p.side y) (glow u) = postage η u.size • marker W p.p (W.tree p.p) u y := by
  obtain ⟨a, i⟩ := u
  rw [show glow _ = _ from above a i, atGrade]
  unfold Initialize.atSite On.stencil
  rw [LinearMap.smul_apply, hp]
  let K : Plaid B a.val := i
  refine congr_arg₂ _ ?_ ?_
  · change (((exp _ : ℝ) : ℂ) ^ a.val)⁻¹ = postage η a.val
    rw [Real.exp_neg, Complex.ofReal_inv, inv_pow, inv_inv, postage, Complex.ofReal_pow]
  change Bare.column (W.tree _) _ _ _ = Bare.column _ _ _ _
  apply congr_arg
  apply Subtype.ext
  rw [LinearMap.comp_apply, On.section_value]
  exact Ensure.physical_dim K

section read
variable (L : Fin n → Glyph (Ensure.deck G) d) (Y : Fin n → Cover)

abbrev profileK (L : Fin n → Glyph B d) : Fin n → Rake.Label B := fun i => ⟨(L i).size, (L i).snd⟩

abbrev Portion (v : Glyph B d) :=
  Glyph B v.size
set_option quotPrecheck false
local notation "𝓚" => (∀ i : Fin n, Portion (L i))

private def stipend (i : Fin n) (z : Portion (L i)) : PowerSeries ℂ :=
  Rescaled.wavesP (A.fees _ (L i).snd) x z

private lemma accumulate (F : Fin n → XSpace.Bare.Series (W.tree p.p) G) :
    Coupling.composeS Ξ (∏ i, F i) = ∏ i, Coupling.composeS Ξ (F i) := by
  have hx (v : Finset (Fin n)) :
    Coupling.composeS Ξ (∏ i ∈ v, F i) = ∏ i ∈ v, Coupling.composeS Ξ (F i) := by
    induction v using Finset.induction with
    | empty =>
      simp only [Finset.prod_empty]
      exact Coupling.comp_unit (share ..)
    | insert a s hi ih => simp only [Finset.prod_insert hi, Coupling.comp_mul (share A.team x), ih]
  exact hx _

private def runeM (z : 𝓚) : PowerSeries ℂ :=
  Coupling.composeS Ξ (Bare.normalized (W.tree _) _ (∏ i, BMenu.marker W p.p (W.tree _) (z i) (Y i)))

def entrance (z : 𝓚) : Option (Fin n) → PowerSeries ℂ
  | none => runeM A W p x L Y z
  | some j => stipend A x L j (z j)

lemma collective (a : Cover) :
    fullRead W x p.p (W.tree _) a A (fun i => Y i - a) (profileK L) Finset.univ =
      ∑ z : 𝓚, ∏ i, entrance A W p x L Y z i := by
  unfold fullRead markArray
  simp_rw [show ∀ i, a + (Y i - a) = Y i from fun _ => by abel]
  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib, Fintype.prod_option]
  unfold Bare.scalar
  rw [← map_prod]
  let Q := ∏ i, stipend A x L i (z i)
  let S := ∏ i, BMenu.marker W p.p (W.tree _) (z i) (Y i)
  change expectation _ _ _ _ (Bare.scalar (W.tree _) Q * _) = runeM A W p x L Y z * Q
  rw [formal_scalars]
  simp_rw [← accumulate]
  rw [comp_expectation]
  exact mul_comm ..

lemma flint (z : 𝓚) (k : Days n) :
    (∏ i : Option (Fin n), coeff (k i) (entrance A W p x L Y z i)) =
      (∏ i : Fin n, oil (A.fees (L i).size (L i).snd) (z i) (k (some i)) x) *
        coeff (k none) (runeM A W p x L Y z) := by
  rw [Fintype.prod_option, mul_comm]
  simp only [entrance, stipend, wavesP, PowerSeries.coeff_mk]

private def raisedG (hp : h ≤ d) (p : Glyph B h) : Glyph B d :=
  ⟨⟨p.fst.val, by
      obtain he := p.1.isLt
      omega⟩,
    p.2⟩

def polyC (r : PowerSeries ℂ) (h : Rooted r) : Module.End ℂ (PowerSeries ℂ) := by
  exact
    { toFun Z := Coupling.composeS r Z,
      map_add' := fun u v => by
        apply PowerSeries.ext
        intro n
        rw [show coeff _ _ = _ from congr_fun (Coupling.explicit h (u + v)).symm n, map_add,
          show Coupling.read (u + v) = Coupling.read u + Coupling.read v from
            funext fun i => map_add _ u v,
          map_add]
        exact
          congr_arg₂ (· + ·) (congr_fun (Coupling.explicit h u) n)
            (congr_fun (Coupling.explicit h v) n),
      map_smul' := fun c u => by
        apply PowerSeries.ext
        intro n
        rw [show coeff _ _ = _ from congr_fun (Coupling.explicit h (c • u)).symm n, RingHom.id_apply,
          map_smul,
          show Coupling.read (c • u) = c • Coupling.read u from funext fun i => map_smul _ c u,
          map_smul]
        exact congr_arg (c • ·) (congr_fun (Coupling.explicit h u) n) }

private lemma reads_z (hp : p.spacing = exp (-η)) (z : 𝓚) :
    let V (i) := raisedG (Nat.le_of_lt_succ (L i).fst.isLt) (z i);
    Coupling.composeS Ξ (point W p d (wrap p.p.side ∘ Y) (fun i => glow (V i))) =
      (∏ i, postage η (z i |>.size)) • runeM A W p x L Y z := by
  intro V
  have hu (i : Fin n) :
    site W p d ((wrap p.p.side ∘ Y) i) (glow (V i)) =
      postage η (z i).size • marker W p.p (W.tree _) (z i) (Y i) :=
    space_at W p η hp (V i) (Y i)
  rw [pointN]
  simp_rw [hu]
  rw [Finset.prod_smul, map_smul]
  exact map_smul (polyC _ (share A.team x)) _ _

/-- Actual point report (before the mesh smear), at arbitrary lifts with common shift. -/
lemma pulse_point (hp : p.spacing = exp (-η)) (a : Cover) (j : ℕ) (y : Fin n → p.Sites)
    (he : y = wrap p.p.side ∘ Y) :
    ∑ b ∈ Normalize.tally j n,
        coeff (b none) (Coupling.composeS Ξ (point W p d y (pulseU b (bets A x η d) (glow ∘ L)))) =
      (∏ i, postage η (L i).size) *
        coeff j (fullRead W x p.p (W.tree _) a A (fun i => Y i - a) (profileK L) Finset.univ) := by
  rw [collective A W p x L Y a, map_sum, Finset.mul_sum]
  let X : (Fin n → Sec G d) → PowerSeries ℂ := fun u => Coupling.composeS Ξ (point W p d y u)
  let Sκ := bets A x η d
  have hx (b : Days n) :
    coeff (b none) (X (pulseU b Sκ (glow ∘ L))) =
      ∑ z : 𝓚,
        (∏ i, postage η (L i).size) *
          (∏ i : Option (Fin n), PowerSeries.coeff (b i) (entrance A W p x L Y z i)) := by
    let Mp :=
      (coeff (b none)).compMultilinearMap
        ((polyC _ (share A.team x)).compMultilinearMap (point W p d y))
    let g (i : Fin n) (z : Portion (L i)) := glow (raisedG (Nat.le_of_lt_succ (L i).fst.isLt) z)
    let m (i : Fin n) (z : Portion (L i)) := dues A x η (h := (L i).size) (L i).2 (b (some i)) z
    change Mp _ = _
    rw [show pulseU b Sκ (glow ∘ L) = fun i => ∑ z : Portion (L i), m i z • g i z from ?_]
    swap
    · funext i
      unfold pulseU Sκ bets
      rw [PowerSeries.coeff_mk]
      dsimp only [Function.comp_def]
      rw [specials, horizon_c]
      rfl
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [MultilinearMap.map_smul_univ]
    have he :
      Coupling.composeS Ξ (point W p d y (fun i => g i (z i))) =
        (∏ i, postage η (z i |>.size)) • runeM A W p x L Y z := by
      conv_lhs => rw [he]
      exact reads_z A W p x η L Y hp z
    change
      (∏ i, m i (z i)) • coeff (b none) (Coupling.composeS Ξ (point W p d y (fun i => g i (z i)))) = _
    rw [he, map_smul, smul_smul, smul_eq_mul, flint, ← mul_assoc, ← Finset.prod_mul_distrib, ←
      Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold m dues
    field_simp [(open_post η ((z i) |>.size))]
  simp_rw [show
      ∀ b : Days n,
        coeff (b none) (Coupling.composeS Ξ (point W p d y (pulseU b (bets A x η d) (glow ∘ L)))) = _
      from hx,
    PowerSeries.coeff_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

lemma pulses (hp : p.spacing = exp (-η)) (a : Cover) (t : Test n) (j : ℕ) :
    realm (bets A x η d) (substitute Ξ (batch W p d)) j n t (glow ∘ L) =
      ∑ y : Fin n → p.Sites,
        write p y t * (∏ i, postage η (L i).size) *
          coeff j
            (fullRead W x p.p (W.tree _) a A (fun i => Lattice.lift (y i) - a) (profileK L)
              Finset.univ) := by
  rw [Normalize.really]
  simp_rw [shifted W p Ξ (share ..)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, mul_assoc]
  apply congr_arg
  exact
    pulse_point A W p x η L (Lattice.lift ∘ y) hp a j y (funext fun i => Eq.symm (wrap_lift (y i)))
end read
end eval
end YM.WilsonMS.Fiscal
