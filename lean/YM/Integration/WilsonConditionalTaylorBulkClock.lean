import YM.Integration.WilsonConditionalTaylorKineticHead
import YM.Integration.WilsonConditionalTaylorKineticRebooking
import YM.Integration.WilsonConditionalTaylorBulkShape

/-! Finite physical subtraction, even coupling scale and rank bounds on
the complete normalized spatial perturbative action. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkClock
open Lattice PowerSeries FormalBulk08 Orb Jets Reef Mesa Shore Lava Wine Bank
open RG Wilson Precision Push.Uniform Stationary
open PhysicalNext.Repeat.Legato MSbar MSbar.Rolling MSbar.Wave MSbar.Midpoint MSbar.Bakery
open WilsonConditionalTaylorKineticRebooking WilsonConditionalTaylorBulkShape
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V : Type} [Fintype V]

def field (v : G.Color) (Y : PathData G) (p : Clip) (U : Pap (wire G n)) : PowerSeries ℝ :=
  primitive v (splitV (PowerSeries.map (MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm).toRingHom U))
    (Wave.ink n p Y)

theorem fresh (v : G.Color) (Y : PathData G) (p : Clip) (U : Pap (wire G n)) : Fresh (field v Y p U) :=
  WilsonConditionalTaylorKineticRebooking.head v _ _ (splitK _)

theorem still (v : G.Color) (Y : PathData G) (p : Clip) (U : Pap (wire G n)) (shape : Ranks U) :
    Still (field v Y p U):=by
  intro e odd
  have pos : 0<e:=by omega
  have extinct : marble 2 (coeff e U)=0:=by
    by_contra nonzero
    have law:=shape e 2 pos nonzero
    omega
  have zero := (marble_eq_zero_iff 2 _).mp extinct
  let link := (WilsonMovingGaussianCoordinates.link G n).symm
  have read : caliper n v (MvPolynomial.rename link (coeff e U))=0:=by
    rw [←WilsonConditionalTaylorKineticProjection.two v (MvPolynomial.rename link (coeff e U)),
      ←MvPolynomial.rename_homogeneousComponent,zero,map_zero,map_zero]
  rw [field,primitive,map_sub,coeff_one,if_neg pos.ne',coeff_C_mul,projection,coeff_mk,splitV,map_sub,
    coeff_C,if_neg pos.ne',sub_zero,coeff_map]
  change 0-_ * caliper n v (MvPolynomial.rename link (coeff e U))=0
  rw [read,mul_zero,sub_zero]

theorem normalHead (A B : PowerSeries ℝ) (T : Pap V) (a : Fresh A) (b : Fresh B) :
    coeff 0 (canter A B V T)=coeff 0 T:=by
  let f:=coeff 0 (canter A B V T)
  let g:=coeff 0 T
  let m:=max f.totalDegree g.totalDegree
  change f=g
  rw [←Wave.buys m f (le_max_left ..),←Wave.buys m g (le_max_right ..)]
  apply Finset.sum_congr rfl
  intro k _
  have same : rancho (canter A B V T) 0 k = rancho T 0 k := by
    rw [stamp_book,paid_nil A B _ k a b]
  exact (marble_grade k f).symm.trans ((congrArg (facade k) same).trans (marble_grade k g))

theorem normalShape (A B : PowerSeries ℝ) (T : Pap V) (a : Still A) (b : Still B)
    (head : (coeff 0 T).IsHomogeneous 2) (shape : Ranks T) : Ranks (canter A B V T):=by
  intro e r pos seen
  rw [stamp_book,Wine.stamp] at seen
  by_contra! fail
  apply seen
  apply Finset.sum_eq_zero
  intro i hi
  have before := Finset.mem_range.mp hi
  by_cases empty : rancho T i r=0
  · rw [empty,smul_zero]
  have rank : r ≤ i + 2 ∧ r % 2 = i % 2 := by
    by_cases old : i=0
    · subst i
      have two : r=2:=by
        by_contra ne
        exact empty ((marble_eq_zero_iff r _).mpr (by rw [MvPolynomial.homogeneousComponent_of_mem head,if_neg ne]))
      omega
    · exact shape i r (by omega) empty
  rw [Wine.bill,(a.pow i|>.mul (b.pow r)) (e-i) (by omega),zero_smul]

theorem actual (v : G.Color) (Y : PathData G) (p : Clip) (U : Pap (wire G n)) (shape : Ranks U)
    (head : (coeff 0 U).IsHomogeneous 2) (civic : Civic U) :
    let H:=field v Y p U
    let C:=canter (bookH H) (bookU H) _ U
    coeff 0 C=coeff 0 U ∧ Ranks C ∧ Civic C :=by
  let H:=field v Y p U
  have first := fresh v Y p U
  have parity := still v Y p U shape
  exact ⟨normalHead _ _ _ (book_fresh H) (book_guard H),
    normalShape _ _ U (even_book H first parity) (even_coupon H first parity) head shape,
    fun s x=>morph _ _ s x (civic s x) (book_equal H)⟩

end YM.Integration.WilsonConditionalTaylorBulkClock

