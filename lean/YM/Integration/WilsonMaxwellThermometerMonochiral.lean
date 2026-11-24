import YM.Integration.WilsonMaxwellThermometerSeven
import YM.Integration.WilsonMaxwellThermometerChiralReading
import YM.Integration.WilsonMaxwellThermometerLines

/-! A monochiral quadratic upper field has zero connected response to two
monochiral squares on every separated physical configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerMonochiral
open Set Function MeasureTheory Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Rose XSpace.Chiral
open WilsonMaxwellThermometerProfile WilsonMaxwellThermometerSeven WilsonMaxwellThermometerChiralSlots
open WilsonMaxwellThermometerChiralReading
open scoped BigOperators
variable {G : Gauge}

def Silent (G : Gauge) {j : ℕ} (s : Bool) (p : Flavor j) :=
  ∀ (i : G.ColorIndex) (a : P) (x : E4), x≠0 → fare i p (slot s a) x=0

theorem initial (s : Bool) (a : P) : Silent G s (slot s a) :=
  fun i b x hx => WilsonMaxwellThermometerLines.vanish x hx i s a b

theorem next {j : ℕ} {s : Bool} {p : Flavor j} (h : Silent G s p) (v : E4) :
    Silent G s (feed v j p) := fun i a _ hx =>
  WilsonMaxwellThermometerLines.derivative i p (slot s a) v (h i a) hx

private theorem loop {j l : ℕ} (s c d : Bool) (p : Flavor j) (q : Flavor l)
    (hp : Silent G s p) (hq : Silent G s q) (a b : P)
    {x y z : E4} (h₁ : x≠y) (h₂ : x≠z) (h₃ : y≠z) :
    triangle G x y z (team G p q) (team G (slot c a) (slot c a))
      (team G (slot d b) (slot d b)) = 0 := by
  let F {k : ℕ} (p : Flavor k) (i : G.ColorIndex) : Factor G := ⟨k,flavor k i p⟩
  unfold team
  simp only [map_sum,LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun i _ => ?_
  change triangle G x y z (letter (F p i) * letter (F q i))
    (letter (F (slot c a) v) * letter (F (slot c a) v))
    (letter (F (slot d b) w) * letter (F (slot d b) w)) = 0
  rw [tri_cost h₁ h₂ h₃]
  have kill {u : ℕ} (t : Bool) (f : Flavor u) (hf : Silent G t f) (e : P)
      {r r' : E4} (hr : r≠r') (m n : G.ColorIndex) :
      linkEntry (r,F f m) (r',F (slot t e) n)=0 := by
    rw [link_eq r r' _ _ hr]
    rw [show K (flavor _ m f) (flavor _ n (slot t e)) r r' =
      (if m=n then (1:ℝ) else 0)*fare m f (slot t e) (r-r') from
        any_ink m f (slot t e) m n (sub_ne_zero.mpr hr), hf m e _ (sub_ne_zero.mpr hr)]
    simp
  by_cases e : c=d
  · subst d; rw [kill c _ (initial c a) b h₃]; ring
  by_cases e' : s=c
  · subst c; rw [kill s _ hp a h₁, kill s _ hq a h₁]; ring
  have ed : s=d := by cases s <;> cases c <;> cases d <;> tauto
  subst d; rw [kill s _ hp b h₂, kill s _ hq b h₂]; ring

theorem coupled {j l : ℕ} (s c d : Bool) (p : Flavor j) (q : Flavor l)
    (hp : Silent G s p) (hq : Silent G s q) (x : Points 3) (hx : x∈conf 3) :
    linked x (polar G c) (polar G d) (team G p q)=0 := by
  have singleton (t : Bool) : upper x (polar G t) 1 1 = 0 ∧ upper x 1 (polar G t) 1 = 0 := by
    have H (a : P) := (quadratic (G:=G) x hx (slot t a) (slot t a)).2
    simp only [upper_triangle, polar, map_sum, LinearMap.sum_apply] at H ⊢
    exact ⟨Finset.sum_eq_zero fun a _ => (H a).1, Finset.sum_eq_zero fun a _ => (H a).2⟩
  have quiet := (quadratic (G:=G) x hx p q).1
  simp only [linked, LinearMap.sub_apply, LinearMap.smul_apply,
    (singleton c).1, (singleton d).2, quiet, mul_zero, zero_smul,
    smul_zero, add_zero, sub_zero]
  simp only [upper_triangle, polar, map_sum, LinearMap.sum_apply]
  have h₁ : x 0≠x 1 := hx.ne (by decide)
  have h₂ : x 0≠x 2 := hx.ne (by decide)
  have h₃ : x 1≠x 2 := hx.ne (by decide)
  exact Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => loop s c d p q hp hq a b h₁ h₂ h₃


end YM.Integration.WilsonMaxwellThermometerMonochiral
