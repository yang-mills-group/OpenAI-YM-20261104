import YM.WilsonMS.Calibration.RStone
import YM.WilsonMS.Calibration.Gateway
import YM.XSpace.KPos
/-!
# Exact B^a regulating matrix before taking the position limit

Wick subtraction at own horizon. Do not assume D(0)=I at finite p. In fact
strict slot lowering corrections permitted; full filtration & H symmetry
in the SAME position dictionary as the target. Barely any topology yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Fiscal
open Function Filter Set Finset MeasureTheory Real
open Lattice XSpace Normalize Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Plane MS.Menus MS.Land MS.Book MS.Book.Convolve MS.Book.Program Theater
open Bin BMenu Rider
open Complex (I)
open PowerSeries (coeff mk constantCoeff)
open scoped Topology ContDiff Interval Classical
variable {G : Gauge} {d h n : ℕ} (A : Prescription (Ensure.deck G)) (x : ℝ)
local notation "B" => Ensure.deck G

abbrev lifted (i : Fin (d + 1)) (v : Plaid B i.val) : Glyph B d :=
  ⟨i, v⟩

def postage (η : ℝ) (h : ℕ) : ℂ :=
  ((exp η) ^ h : ℝ)

lemma open_post (η : ℝ) (h : ℕ) : postage η h ≠ 0 :=
  Complex.ofReal_ne_zero.mpr ((pow_pos (exp_pos _) _).ne')

variable (η : ℝ)

def dues (u : Plaid B h) (k : ℕ) (i : Glyph B h) : ℂ :=
  (postage η h / postage η i.size) * oil (A.fees h u) i k x

lemma real_due (u : Plaid B h) (k : ℕ) (i : Glyph B h) : star (dues A x η u k i) = dues A x η u k i := by
  unfold dues
  rw [star_mul', star_div₀,
    show ∀ k : ℕ, star (postage η k) = postage η k from fun k => Complex.conj_ofReal _,
    show star (postage η i.size) = postage η i.size from Complex.conj_ofReal _, oil]
  simp
section spectrum

def glow (i : Glyph B d) : Sec G d :=
  ⟨Letters B i, indoor B i⟩

lemma above (i : Fin (d + 1)) (u : Plaid B i.val) :
    glow (lifted i u) = en (Nat.le_of_lt_succ i.isLt) (Ensure.full u) :=
  rfl

lemma shines (u : Glyph B d) : Daylight B d u = glow u :=
  readHeight ..

lemma catches (u : Glyph B d) : reel d (glow u) = glow u :=
  Subtype.ext (real_shell ..)

lemma turn (u : Plaid B d) (s : Signed) :
    ori s.ortho d (glow (Land.read u)) = ∑ i : Plaid B d, (beta s u i : ℂ) • glow (Land.read i) := by
  let V := Maxwell.observable G d
  let L := V.restrictScalars ℝ
  have ht : reflectPol s.ortho (Letters B (Land.read u)) = V (Labels.tensor s.ortho (labelK u)) :=
    (pulls_label (labelK u) s.ortho).symm
  apply Subtype.ext
  change reflectPol s.ortho (Letters B (Land.read u)) = _
  rw [ht, paper]
  change L _ = (shellSector G d).subtype _
  simp only [map_sum, map_smul]
  rfl

lemma plunge (s : Signed) (i : Fin (d + 1)) (p q : Plaid B i.val) :
    beta s p q = lines s (lifted i p) (lifted i q) := by
  rcases p with ⟨a, p⟩
  rcases q with ⟨b, q⟩
  by_cases he : a = b
  · subst b
    exact (Bin.beta_c s a p q).trans (common s i a p q |>.symm)
  rw [show beta s _ _ = 0 from
      Classical.byContradiction (fun h => he (passes s ⟨a, p⟩ (⟨b, q⟩ : Plaid B i.val) h))]
  exact Eq.symm (Classical.byContradiction (fun h => he (Fin.ext (bins s _ _ h |>.2))))

lemma turns (p : Glyph B d) (s : Signed) :
    ori s.ortho d (glow p) = ∑ i : Glyph B d, (lines s p i : ℂ) • glow i := by
  obtain ⟨a, b⟩ := p
  let y : Plaid B a.val := b
  let V := up (G := G) (Nat.le_of_lt_succ a.isLt)
  have ht : V (glow (Land.read y)) = glow (lifted a y) := rfl
  have he := congr_arg V (turn y s)
  rw [map_sum] at he
  refine Eq.trans (show ori s.ortho d (glow ⟨a, b⟩) = _ from he) ?_
  symm
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single a]
  · exact
      Finset.sum_congr rfl fun j _ => by
        rw [map_smul, plunge]
        rfl
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro j _
    rw [show lines s ⟨a, b⟩ ⟨u, j⟩ = 0 from
        Classical.byContradiction fun h => hu (Fin.ext (bins s _ _ h |>.1.symm)),
      Complex.ofReal_zero, zero_smul]
  simp
end spectrum

def payment (i : Plaid B d) (k : ℕ) : Sec G d :=
  ∑ j : Glyph B d, dues A x η i k j • glow j

def tax (d : ℕ) (i : ℕ) : On.Grade G d →ₗ[ℂ] Sec G d :=
  (Ensure.stars G d).constr ℂ (fun p => payment A x η p i)

lemma ears (d : ℕ) (i : ℕ) (p : Plaid B d) : tax A x η d i (Ensure.full p) = payment A x η p i := by
  rw [← Ensure.stars_eq, tax, Module.Basis.constr_basis]

def debt (d i : ℕ) : FieldEnd G d :=
  (Daylight B d).constr ℂ fun c =>
    up (Nat.le_of_lt_succ c.fst.isLt) (payment A x η c.2 i (d := c.size))

lemma specials (v : Glyph B d) (i : ℕ) :
    debt A x η d i (glow v) = up (Nat.le_of_lt_succ v.1.isLt) (payment A x η v.2 i (d := v.size)) :=
  by rw [← shines, debt, Module.Basis.constr_basis]

lemma savings (v : Glyph B h) (i : ℕ) (H : h ≤ d) :
    debt A x η d i (up H (glow v)) = up H (debt A x η h i (glow v)) := by
  let a : Glyph B d :=
    ⟨⟨v.1.val, by
        obtain ht := v.1.isLt
        omega⟩,
      v.2⟩
  rw [show up H _ = glow a from rfl, specials, specials]
  rfl

lemma compatible (i : ℕ) (H : h ≤ d) (v : Sec G h) :
    debt A x η d i (up H v) = up H (debt A x η h i v) := by
  rw [← (Daylight B h).sum_repr v]
  simp_rw [map_sum, map_smul, shines, savings]

lemma pure_rate (d : ℕ) (k : ℕ) (i : Plaid B d) :
    debt A x η d k (glow (Land.read i)) = payment A x η i k :=
  specials ..

lemma horizon_c (h : d ≤ n) (i : Plaid B d) (k : ℕ) :
    up h (payment A x η i k) =
      ∑ j : Glyph B d,
        dues A x η i k j •
          glow
            (⟨⟨j.1.val, by
                  have h := j.1.isLt
                  omega⟩,
                j.2⟩ :
              Glyph B n) := by
  unfold payment
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

lemma sign0 (i : Plaid B h) (j : Glyph B h) (hv : i.1.val ≤ j.grade) :
    dues A x η i 0 j = if j = Land.read i then 1 else 0 := by
  have hz := (A.init h i).Single j hv
  unfold dues oil
  rw [hz]
  split_ifs with H
  · subst j
    rw [show (Land.read i).size = h from rfl, div_self (open_post η h)]
    simp
  simp

lemma lower (n : ℕ) (v : Glyph B d) (h : v.grade < n) : ((debt A x η d 0 - 1) ^ n) (glow v) = 0 := by
  let P := debt A x η d 0
  let V := P - 1
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
    obtain ⟨a, b, x'⟩ := v
    let v : Plaid B a.val := ⟨b, x'⟩
    let W := glow (Land.read v)
    let T := up (G := G) (Nat.le_of_lt_succ a.isLt)
    change (V ^ (n + 1)) (T W) = _
    rw [pow_succ, Module.End.mul_apply, show V (T W) = T (payment A x η v 0) - T W from ?_]
    swap
    · change debt _ _ _ _ _ _ - _ = _
      rw [compatible, pure_rate]
      rfl
    let f i := dues A x η v 0 i • glow i
    let s := Finset.univ.erase (Land.read v)
    have he : T (payment A x η v 0) - T W = ∑ i ∈ s, T (f i) := by
      unfold payment
      rw [map_sum]
      change (∑ i : Glyph B a.val, T (f i)) - _ = _
      rw [← Finset.add_sum_erase _ (fun i => T (f i)) (mem_univ (Land.read v))]
      apply add_left_cancel (a := T W)
      unfold f
      rw [sign0 _ _ _ v (Land.read v) (le_refl _), if_pos rfl, one_smul]
      change T _ + ((_ + _) - _) = _
      abel
    rw [he, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases ht : i.grade < n
    · obtain ⟨j, p⟩ := i
      let a' : Fin (d + 1) :=
        ⟨j.val, by
          obtain hf := a.isLt
          obtain h := j.isLt
          omega⟩
      let y : Glyph B d := ⟨a', p⟩
      unfold f
      rw [map_smul, map_smul, show (V ^ n) (T _) = (V ^ n) (glow y) from rfl, ih y ht, smul_zero]
    unfold f
    rw [sign0 _ _ _ v i
        (by
          change v.fst.val < n + 1 at h
          omega),
      if_neg (Finset.mem_erase.mp hi |>.1), zero_smul, map_zero, map_zero]

lemma invert (d : ℕ) : Bijective (debt A x η d 0) := by
  let Z := debt A x η d 0
  have h : IsNilpotent (Z - 1) := by
    refine ⟨d + 1, (Daylight B d).ext fun i => ?_⟩
    rw [shines]
    refine lower A x η _ _ ?_
    exact Nat.lt_add_one_of_le (Glyph.memory _)
  have hp : IsUnit Z := by
    obtain he := IsNilpotent.isUnit_add_one (R := Module.End ℂ (Sec G d)) (r := Z - 1) h
    exact (show Z = (Z - 1) + 1 from (sub_add_cancel Z 1).symm) ▸ he
  exact (Module.End.isUnit_iff _).mp hp

variable (hA : Commuting A)
include hA

lemma post_leaf (d i : ℕ) : debt A x η d i (leaf G d) = if i = 0 then leaf G d else 0 := by
  have he (b : Glyph B 0) : debt A x η 0 i (glow b) = if i = 0 then glow b else 0 := by
    obtain ⟨j, rfl⟩ := Rider.no_size b
    rw [pure_rate, payment]
    simp only [dues, oil, hA.unit, bareG]
    by_cases hi : i = 0
    swap
    · simp [hi]
    subst i
    simp [postage, apply_ite (Polynomial.eval x)]
    simp [apply_ite Complex.ofReal]
  let U := up (G := G) (Nat.zero_le d)
  let L := leaf G 0
  change debt _ _ _ _ i (U L) = if i = 0 then U L else 0
  rw [compatible (H := Nat.zero_le d)]
  rw [← (Daylight B 0).sum_repr L]
  simp_rw [map_sum, map_smul, shines, he]
  split_ifs with hx <;>
    first
    | rfl
    | simp

omit hA in
lemma post_reel (i : ℕ) (p : Sec G d) : debt A x η d i (reel d p) = reel d (debt A x η d i p) := by
  rw [← (Daylight B d).sum_repr p]
  simp_rw [map_sum, map_smulₛₗ, shines, catches, specials]
  simp only [RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [horizon_c]
  simp_rw [map_sum, map_smulₛₗ, catches, starRingEnd_apply, real_due]

lemma rotate_rates (s : Signed) (i : Plaid B h) (k : ℕ) (v : Glyph B h) :
    ∑ j : Plaid B h, (beta s i j : ℂ) * dues A x η j k v =
      ∑ j : Glyph B h, dues A x η i k j * (lines s j v : ℂ) := by
  let V := A.fees h
  let P (u : Glyph B h) := postage η h / postage η u.size
  let g (a : Plaid B h) (b : Glyph B h) : ℝ := ((V a k).register b).eval x
  have hs := hA.field_shift h s i k v
  rw [ledger] at hs
  have ht : ∑ j : Plaid B h, beta s i j * g j v = ∑ j : Glyph B h, lines s j v * g i j := by
    obtain hu := congr_arg (Polynomial.eval x) hs
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul] at hu
    exact hu.symm
  have hm :
    ∑ j : Plaid B h, (beta s i j : ℂ) * dues A x η j k v =
      P v * (↑(∑ j : Plaid B h, beta s i j * g j v) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_mul]
    exact mul_left_comm ..
  rw [hm, ht, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hh => ?_
  by_cases he : lines s j v = 0
  · simp [he]
  have hl : P v = P j := congr_arg (fun n => postage η h / postage η n) (bins s j v he |>.1.symm)
  rw [hl, Complex.ofReal_mul]
  change _ = (P j * (g i j : ℂ)) * _
  ring

lemma handed (s : Signed) (t : ℕ) (p : Sec G d) :
    ori s.ortho d (debt A x η d t p) = debt A x η d t (ori s.ortho d p) := by
  let F (d : ℕ) := debt A x η d t
  have he (h) (p : Plaid B h) :
    ori s.ortho h (F h (glow (Land.read p))) = F h (ori s.ortho h (glow (Land.read p))) := by
    unfold F
    rw [turn, pure_rate, map_sum]
    simp_rw [payment, map_sum, map_smul, turns, pure_rate]
    simp_rw [payment, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact
      Finset.sum_congr rfl fun i _ => by
        rw [← Finset.sum_smul, ← Finset.sum_smul, rotate_rates A x η hA]
  rw [← (Daylight B d).sum_repr p]
  simp_rw [map_sum, map_smul, shines]
  apply Finset.sum_congr rfl
  intro X _
  apply congr_arg
  obtain ⟨v, i⟩ := X
  let hx := Nat.le_of_lt_succ v.isLt
  let z := glow (Land.read (G := G) («B» := Ensure.deck G) (d := v.val) i)
  have ht (x : Sec G v.val) : ori s.ortho d (up hx x) = up hx (ori s.ortho v.val x) := rfl
  change ori s.ortho d (debt _ _ _ d t (up hx z)) = debt _ _ _ d t (ori s.ortho d (up hx z))
  rw [ht, compatible, compatible, ht]
  exact congr_arg (up hx) (he v.val i)

lemma vAxis (d i : ℕ) : debt A x η d i - (coeff i 1 : FieldEnd G d) ∈ Change G d := by
  rw [may_change]
  simp_rw [PowerSeries.coeff_one, LinearMap.sub_apply]
  split_ifs with he
  · subst i
    simp only [Module.End.one_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [post_leaf A x η hA, if_pos rfl, sub_self]
    · intro k hk p hp
      let z : Sec G k := ⟨p.val, hp⟩
      rw [show p = up hk z from rfl, compatible]
      exact Submodule.sub_mem _ (debt A x η k 0 z).property hp
    · intro p
      rw [map_sub, post_reel]
    intro s p
    rw [map_sub, handed A x η hA s]
  simp only [LinearMap.zero_apply, sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [post_leaf A x η hA, if_neg he]
  · intro k hk p hp
    let z : Sec G k := ⟨p.val, hp⟩
    rw [show p = up hk z from rfl, compatible]
    exact (debt A x η k i z).property
  · exact fun p => post_reel ..
  exact fun s p => (handed A x η hA s i p).symm
omit hA

def bets (d : ℕ) : Guard G d :=
  PowerSeries.mk (debt A x η d)
include hA

lemma pPrice (d : ℕ) : Normalize.Formal (bets A x η d) := by
  let U := debt A x η d
  let P (i : ℕ) : Change G d := ⟨U i - (coeff i 1 : FieldEnd G d), vAxis A x η hA d i⟩
  have ht : stand (P 0) = U 0 := by
    change 1 + (U 0 - _) = _
    rw [PowerSeries.coeff_one, if_pos rfl]
    abel
  rw [show bets A x η d = deck P from ?_]
  · exact formal_deck P (ht.symm ▸ invert A x η d)
  refine PowerSeries.ext fun n => ?_
  rw [bets, PowerSeries.coeff_mk, decked, pulling]
  split_ifs with hx
  subst n
  exact ht.symm
  change U n = U n - (coeff n 1 : FieldEnd G d)
  rw [PowerSeries.coeff_one, if_neg hx]
  exact (sub_zero (U n)).symm
end YM.WilsonMS.Fiscal
