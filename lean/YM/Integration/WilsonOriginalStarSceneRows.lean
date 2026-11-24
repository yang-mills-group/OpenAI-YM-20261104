import YM.Integration.WilsonOriginalStarSceneWords
import YM.Integration.WilsonOriginalCompensatedPortfolio

/-! The independent finite source rows, including the clear marked constant.
Their salary and vote are assigned before any particular test is read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarSceneRows
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Push Push.AbsoluteSums
open Earn Sunrise PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V → ℕ) {n : Side} (o : V → Site n)

def binder (j : V) : Binder (Passport.point o) (Stock.census V) where
  mode := (Stock.census V).fire j
  front := j
  east := mem_singleton_self _
  path _ := []
  span v hv := by
    obtain rfl : v=j := mem_singleton.mp hv
    rfl
  extra := 0

theorem length (j : V) : (binder o j).length = 0 := by
  simp [Binder.length,Binder.distance,binder,Passport.point,Census.fire]

variable (σ g τ : ℝ) (v : (j:V) → R.family.label (d j)) (t : V → T → ℂ)
local notation "Λ" => scalar R d g τ v

def wage (i : Entry R d) := 1 + normalizer (raw R d i) σ * ‖Λ i‖

def rows (i : Entry R d) : Row (Passport.point o) (Stock.census V) G T where
  binder := binder o (root R d i)
  lamp := loan R d i
  atom := unitAtom (raw R d i) σ
  lawful := invariant _ _ (lawful R d i)
  clear := constant R d i
  salary := wage R d σ g τ v i
  sound := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (positive _ _).le (norm_nonneg _))
  paint x := ((normalizer (raw R d i) σ : ℝ):ℂ) * Λ i * t (root R d i) x
  rank := clear R d i

local notation "M" => rows R d o σ g τ v t

theorem honored (ht : ∀i x,‖t i x‖≤1) (i : Entry R d) : (M i).Budget := by
  intro x
  change ‖((normalizer (raw R d i) σ:ℝ):ℂ)*Λ i*t (root R d i) x‖ ≤ 1+_
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive _ _)]
  exact (mul_le_of_le_one_right (mul_nonneg (positive _ _).le (norm_nonneg _)) (ht _ _)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem original (j : ℕ) (grade : maximum R d ≤ j) :
    Issues M σ j (fun _=>tariff R d) := by
  refine ⟨fun i=>unitPrice _ _,fun i=>⟨?_ ,?_⟩⟩
  · change rank R d i - pole R d i ≤ j
    exact (Nat.sub_le _ _).trans ((le_sup (f:=rank R d) (mem_univ i)).trans grade)
  · change tariff R d = ∑ v∈({root R d i}:Finset V), (fun _ : V=>tariff R d) v
    simp

def bill (w : V → ℝ) := ∑i:Entry R d,w (root R d i)* (wage R d σ g τ v i *
    Real.exp (σ*(raw R d i).length))

theorem offers (w : V → ℝ) (hw : ∀i,0<w i) : Offers M w σ (bill R d σ g τ v w) := by
  intro x
  let price (i:Entry R d):=w (root R d i)*(wage R d σ g τ v i*Real.exp (σ*(raw R d i).length))
  have non (i:Entry R d):0≤price i:=
    mul_nonneg (hw _).le (mul_nonneg (M i).sound.le (Real.exp_nonneg _))
  have booked (i:Entry R d): Poly.toll w (M i).mode*(M i).height σ=price i:=by
    change (∏ k∈({root R d i}:Finset V),w k) *(_*Real.exp (σ*↑((binder o (root R d i)).length + (raw R d i).length)))=_
    simp [length,price,rows]
  refine ⟨fun i=>?_,(hasSum_fintype _).summable,?_⟩
  · change 0 ≤ if (M i).center=x then Poly.toll w (M i).mode*(M i).height σ else 0
    split
    · rw [booked]
      exact non _
    · exact le_rfl
  · rw [tsum_fintype]
    exact sum_le_sum fun i _=>by
      split
      · exact (booked i).le
      · exact non i

theorem fleet (w : V → ℝ) (hw : ∀i,0<w i) (ht : ∀i x,‖t i x‖≤1)
    (order pieces shelf : ℕ) (fit : maximum R d≤order)
    (count : Fintype.card V≤pieces) (crew : Fintype.card V * tariff R d ≤ shelf) :
    Scene.Armada M w (fun _=>tariff R d) σ (bill R d σ g τ v w) order pieces shelf := by
  refine ⟨⟨fun j=>j.val.card_le_univ.trans count,fun j=>?_⟩,hw,offers R d o σ g τ v t w hw,
    original R d o σ g τ v t order fit,honored R d o σ g τ v t ht⟩
  simpa using (Nat.mul_le_mul_right (tariff R d) j.val.card_le_univ).trans crew

end YM.Integration.WilsonOriginalStarSceneRows
