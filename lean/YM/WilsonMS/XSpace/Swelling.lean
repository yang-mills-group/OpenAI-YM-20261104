import YM.WilsonMS.XSpace.LeadingFrame
/-!
# Coupling substitution and the physical frame diagram

Frames act *before* evaluation. They form a real subgroup, so cannot use
formal substitution by a possibly complex series to prove they remain in
the allowed orbit. Visible real checks (`Clean`). Keep no assumptions on
scales or bounded derivatives here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Sea
open Function Set Filter MeasureTheory Real Finset
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus
open Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu VisitH
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical
variable {G : Gauge} {d n j k : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable {Y S : Guard G d}

def coupon (c : Cn) (P : Guard G d) : Guard G d :=
  mk (substitute c (fun i => PowerSeries.coeff i P))

def Clean (c : Cn) :=
  ∀ j, star (coeff j c) = coeff j c
variable {c : Cn}

lemma copy_clean (A : Team) (x : ℝ) : Clean (Program.shift A x) := by
  intro j
  unfold Program.shift
  rw [PowerSeries.coeff_mk]
  split <;>
    first
    | simp only [star_zero]
    | (split <;>
          first
          | simp only [star_one _]
          | exact Complex.conj_ofReal _)

lemma Clean.mul {p : Cn} (hv : Clean p) (h : Clean c) : Clean (p * c) := by
  intro i
  rw [PowerSeries.coeff_mul]
  simp_rw [star_sum, star_mul', h _, hv _]

lemma Clean.one : Clean 1 := by
  intro i
  simp only [PowerSeries.coeff_one]
  split <;> simp

lemma Clean.powers (h : Clean c) (i : ℕ) : Clean (c ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero]
    exact Clean.one
  | succ i ih =>
    rw [pow_succ]
    exact ih.mul h

lemma Clean.payment (h : Clean c) (i j : ℕ) : cut c i j = (((cut c i j).re : ℝ) : ℂ) := by
  have he : (star (cut c i j)).im = (cut c i j).im := congr_arg Complex.im ((Clean.powers h i) j)
  apply Complex.ext
  rfl
  change _ = 0
  change -_ = _ at he
  linarith

lemma turn0 (c : Cn) : constantCoeff (coupon c Y) = constantCoeff Y := by
  rw [coupon, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, pay0,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma turn_height (p : Pick G d) (h : Clean c) (j : ℕ) (hx : j ≠ 0) :
    coeff j (coupon c (deck p)) ∈ Change G d := by
  unfold coupon
  rw [PowerSeries.coeff_mk, rules]
  refine Submodule.sum_mem _ fun i hi => ?_
  by_cases ht : i = 0
  · subst i
    rw [cut, pow_zero, PowerSeries.coeff_one, if_neg hx, zero_smul]
    exact Submodule.zero_mem _
  rw [pos_decked _ ht, Clean.payment h i j,
    show ∀ (t : ℝ) (U : FieldEnd G d), (t : ℂ) • U = t • U from fun t x =>
      IsScalarTower.algebraMap_smul ℂ t x]
  exact Submodule.smul_mem (Change G d) _ (p i).property

lemma makeDeck {P : Guard G d} (a : Change G d) (ht : IsUnit (constantCoeff P))
    (hp : constantCoeff P = stand a) (h : ∀ (i : ℕ), i ≠ 0 → coeff i P ∈ Change G d) : Formal P := by
  refine ⟨?_, (PowerSeries.isUnit_iff_constantCoeff (R := FieldEnd G d)).mpr ht⟩
  let T := fun i => if hx : i = 0 then a else (⟨coeff i P, h i hx⟩ : Change G d)
  refine ⟨T, PowerSeries.ext fun i => ?_⟩
  rw [decked]
  unfold pulling
  unfold T
  split_ifs with he
  · subst i
    exact (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans hp
  rfl

lemma turn_seed (hp : Formal Y) (h : Clean c) : Formal (coupon c Y) := by
  obtain ⟨⟨p, hp⟩, hs⟩ := hp
  apply makeDeck (p 0)
  · rw [turn0]
    exact (PowerSeries.isUnit_iff_constantCoeff (R := FieldEnd G d)).mp hs
  · rw [turn0, hp, const_deck]
  rw [hp]
  exact fun i hi => turn_height p h i hi

lemma enlist (c : Cn) (t : Test n) (p : Fin n → Sec G d) (F : Reports G d) (j : ℕ) :
    substitute c (fun i => F i n t p) j = substitute c F j n t p := by
  simp_rw [rules, Finset.sum_apply, LinearMap.sum_apply, _root_.sum_apply, Pi.smul_apply,
    LinearMap.smul_apply, smul_apply]

lemma cite_r (h : Rooted c) (t : Test n) (p : Fin n → Sec G d) (F : Reports G d) :
    said (substitute c F) t p = Coupling.composeS c (said F t p) := by
  apply PowerSeries.ext
  intro i
  rw [show coeff i (said (substitute c F) t p) = substitute c F i n t p from PowerSeries.coeff_mk ..,
    ← enlist,
    show (fun i => F i n t p) = Coupling.read (said F t p) from
      funext fun i => Eq.symm (PowerSeries.coeff_mk ..)]
  exact congr_fun (Coupling.explicit h (said F t p)) i

lemma coupon_paid (h : Rooted c) (p : Sec G d) (j : Dime G d) :
    Normalize.tax (coupon c S) p j = Coupling.composeS c (Normalize.tax S p j) := by
  apply PowerSeries.ext
  intro i
  rw [show coeff i _ = substitute c (Coupling.read (Normalize.tax S p j)) i from
      (congr_fun (Coupling.explicit h (Normalize.tax S p j)) i).symm]
  unfold coupon Normalize.tax
  simp_rw [PowerSeries.coeff_mk, rules, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply,
    Coupling.read, PowerSeries.coeff_mk, LinearMap.smul_apply, map_smul, Finsupp.smul_apply]

lemma advertise (h : Rooted c) (S : Guard G d) (F : Reports G d) :
    realm (coupon c S) (substitute c F) = substitute c (realm S F) := by
  let L :=
    PowerSeries.substAlgHom (R := ℂ)
      (PowerSeries.HasSubst.of_constantCoeff_zero (Coupling.const_coupling (S := ℂ) h))
  have he (n : ℕ) (t : Test n) (p : Fin n → Sec G d) :
    said (realm (coupon c S) (substitute c F)) t p = said (substitute c (realm S F)) t p := ?h
  swap
  · rw [talks, cite_r h t p, talks]
    simp_rw [coupon_paid h, cite_r h,
      show ∀ p : PowerSeries ℂ, Coupling.composeS c p = L p from fun p => by
        unfold Coupling.composeS L
        rw [PowerSeries.coe_substAlgHom],
      map_sum, map_mul, map_prod]
  ext1 n
  ext1 k
  ext1 t
  ext1 p
  have hx := congr_arg (coeff n) (he k t p)
  simpa only [said, PowerSeries.coeff_mk] using hx

lemma costRoot (h : Clean c) (A : Screen G d) (L : Pick G d) (R : Reports G d)
    (hp : Screen.Solved A L R) (hx : Rooted c) (p : Pick G d) (ht : deck p = coupon c (deck L)) :
    Screen.Solved A p (Program.substitute c R) := by
  intro m
  rw [ht, advertise hx, rules, map_sum]
  by_cases hu : m = 0
  · subst m
    rw [show Finset.Iic (0 : ℕ) = {0} from Finset.ext (by simp), Finset.sum_singleton, cut, pow_zero,
      PowerSeries.coeff_one, if_pos rfl, one_smul]
    exact hp _
  rw [if_neg hu]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h0 : j = 0
  · subst j
    rw [cut, pow_zero, PowerSeries.coeff_one, if_neg hu, zero_smul, map_zero]
  rw [Clean.payment h j m]
  rw [show ∀ (t : ℝ) (U : Prediction G d), (t : ℂ) • U = t • U from fun t x =>
      IsScalarTower.algebraMap_smul ℂ t x,
    map_smul, hp j, if_neg h0, smul_zero]
end YM.WilsonMS.Sea
