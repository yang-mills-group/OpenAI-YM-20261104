import YM.Integration.WilsonOriginalNamedRelativeRows

/-! The cost of all ordered angular sites of one genuine group word is independent of its torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalResidentAngles
open Finset Lattice RG Wilson Marker Push Push.AbsoluteSums Animals QuadraticLocal QuadraticLocal.Earn
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V α:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

abbrev Seats (A:Row o J G α) (D:Type) (r:ℕ) := Fin r→(A.atom.footprint A.center)×D

def sites {A:Row o J G α} {D:Type} {r:ℕ} (a:Seats A D r) : Finset (Site n) :=
  univ.image fun j=>(a j).1.val

theorem supported {A:Row o J G α} {D:Type} {r:ℕ} (a:Seats A D r) :
    sites a ⊆ A.atom.footprint A.center := by
  rintro _ occ
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp occ
  exact (a j).1.property

theorem census (A:Row o J G α) (D:Type) [Fintype D] (r:ℕ) :
    Fintype.card (Seats A D r) ≤ (ballCost A.length * Fintype.card D)^r := by
  have inside:A.atom.footprint A.center ⊆ neighbors A.length A.center:=by
    intro u present
    exact (neighbors_mem ..).mpr (A.binder.spread A.atom (A.binder.footprint A.atom present))
  have paid:=(card_le_card inside).trans (neighbors_card A.length A.center)
  calc
    _=((A.atom.footprint A.center).card*Fintype.card D)^r:=by simp [Seats]
    _≤_:=Nat.pow_le_pow_left (Nat.mul_le_mul_right _ paid) _

def fare (b:ℝ) (d r:ℕ) : ℝ :=
  (d:ℝ)^r*(2/b)^(4*r)*(4*r).factorial*Real.exp (b/2)

theorem nonneg (b:ℝ) (hb:0<b) (d r:ℕ) : 0≤fare b d r := by unfold fare; positivity

theorem polynomial (b:ℝ) (hb:0<b) (l d r:ℕ) :
    ((ballCost l*d)^r:ℕ) ≤ fare b d r*Real.exp (b*l) := by
  let k:=4*r
  have half:0≤b*((l:ℝ)+1/2):=by positivity
  have exp:=(div_le_iff₀ (show 0<((k.factorial:ℕ):ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp (b*((l:ℝ)+1/2)) half k)
  have compound:(2:ℝ)*(l:ℝ)+1=(2/b)*(b*((l:ℝ)+1/2)):=by field_simp
  calc
    (((ballCost l*d)^r:ℕ):ℝ)= (d:ℝ)^r*(2*(l:ℝ)+1)^k:=by
      simp only [ballCost,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow,k,pow_mul]
      ring
    _ = (d:ℝ)^r*(2/b)^k*(b*((l:ℝ)+1/2))^k:=by rw [compound,mul_pow];ring
    _ ≤ (d:ℝ)^r*(2/b)^k*(Real.exp (b*((l:ℝ)+1/2))*k.factorial):=
      mul_le_mul_of_nonneg_left exp (by positivity)
    _ = _:=by
      rw [show b*((l:ℝ)+1/2)=b/2+b*l by ring,Real.exp_add]
      unfold fare
      ring

theorem volume (A:Row o J G α) (D:Type) [Fintype D] (r:ℕ) (b:ℝ) (hb:0<b) :
    (Fintype.card (Seats A D r):ℝ)≤fare b (Fintype.card D) r * Real.exp (b*A.length) :=
  (Nat.cast_le.mpr (census A D r)).trans (polynomial b hb A.length (Fintype.card D) r)

end YM.Integration.WilsonOriginalResidentAngles
