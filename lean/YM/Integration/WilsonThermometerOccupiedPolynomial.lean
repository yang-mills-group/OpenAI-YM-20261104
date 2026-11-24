import YM.Integration.WilsonThermometerMixedAmplitude

/-! Count occupied hard factors in an actual packet while every quiet factor stays in its original slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedPolynomial
open Marker Finset
open scoped Classical BigOperators
variable {R : Census (Fin 3)}

def Order (n : ℕ) (a : Poly R) : Prop := ∀ s:R.Mode, s.val.card < n → a.part s = 0

theorem nil (n:ℕ) : Order n (0:Poly R) := fun s _ => Poly.part_nil s

theorem zero (a:Poly R) : Order 0 a := fun _ h => (Nat.not_lt_zero _ h).elim

theorem plus {a b:Poly R} {n:ℕ} (ha:Order n a) (hb:Order n b) : Order n (a+b) := by
  intro s hs
  rw [Poly.part_plus,ha s hs,hb s hs,zero_add]

theorem times {a b:Poly R} {l k:ℕ} (ha:Order l a) (hb:Order k b) : Order (l+k) (a*b) := by
  intro s hs
  rw [Poly.part_mul]
  apply sum_eq_zero
  intro j _
  apply sum_eq_zero
  intro t _
  split
  next merged =>
    have span:j.val.card+t.val.card=s.val.card:=by rw [←card_union_of_disjoint merged.1,merged.2]
    by_cases left:j.val.card<l
    · rw [ha j left,zero_mul]
    · rw [hb t (by omega),mul_zero]
  next => rfl

theorem empty {a:Poly R} (h:Order 4 a):a=0 := by
  ext1 s
  have size:s.val.card≤3:=card_le_univ _
  exact (h s (by omega)).trans (Poly.part_nil s).symm

structure Cubic (F:ℂ→Poly R) where
  a : Poly R
  b : Poly R
  c : Poly R
  d : Poly R
  linear : Order 1 b
  quadratic : Order 2 c
  cubic : Order 3 d
  value z : F z = a+Poly.bead R z*b+(Poly.bead R z)^2*c+(Poly.bead R z)^3*d

def constant (a:Poly R):Cubic (fun _=>a) :=
  ⟨a,0,0,0,nil _,nil _,nil _,fun _=>by simp⟩

def attach {F:ℂ→Poly R} (C:Cubic F) (a d:Poly R) (paid:Order 1 d):
    Cubic (fun z=>F z*(a+Poly.bead R z*d)) where
  a:=C.a*a
  b:=C.a*d+C.b*a
  c:=C.b*d+C.c*a
  d:=C.c*d+C.d*a
  linear:=plus (times (zero C.a) paid) (times C.linear (zero a))
  quadratic:=plus (times C.linear paid) (times C.quadratic (zero a))
  cubic:=plus (times C.quadratic paid) (times C.cubic (zero a))
  value z:=by
    rw [C.value]
    let t:=Poly.bead R z
    have gone:C.d*d=0:=empty (times C.cubic paid)
    calc
      _ = C.a*a+t*(C.a*d+C.b*a)+t^2*(C.b*d+C.c*a)+t^3*(C.c*d+C.d*a)+t^4*(C.d*d) := by
        dsimp only [t]
        ring
      _ = _ :=by rw [gone,mul_zero,add_zero]

theorem product {ι:Type*} (a d:ι→Poly R) (keep:∀i,Order 1 (d i)) (S:Finset ι):
    Nonempty (Cubic (fun z=>∏i∈S,(a i+Poly.bead R z*d i))) :=by
  induction S using Finset.induction_on with
  | empty =>simpa only [Finset.prod_empty] using (show Nonempty (Cubic (fun _=>1:ℂ→Poly R)) from ⟨constant 1⟩)
  | @insert i S fresh ind =>
    obtain ⟨C⟩:=ind
    have prod (z:ℂ): (∏j∈insert i S,(a j+Poly.bead R z*d j)) =
        (∏j∈S,(a j+Poly.bead R z*d j))*(a i+Poly.bead R z*d i):= by rw [Finset.prod_insert fresh,mul_comm]
    simp_rw [prod]
    exact ⟨attach C (a i) (d i) (keep i)⟩

theorem beadPower (z:ℂ) (a:Poly R) (d:ℕ): (Poly.bead R z)^d*a=(z^d) • a:=by
  induction d with
  | zero =>simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,Poly.product_bead,smul_smul,pow_succ']

theorem read {F:ℂ→Poly R} (C:Cubic F) (s:R.Mode) (z:ℂ):
    (F z).part s=C.a.part s+z*C.b.part s+z^2*C.c.part s+z^3*C.d.part s:=by
  rw [C.value,Poly.product_bead,beadPower,beadPower]
  simp only [Poly.part_plus,Poly.part_smul]

end YM.Integration.WilsonThermometerOccupiedPolynomial
