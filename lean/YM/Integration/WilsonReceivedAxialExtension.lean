import YM.Integration.WilsonReceivedWholeFieldMask
import YM.Integration.WilsonRegisteredFlatLocal

/-! A locally cold lifted box gives one genuine healthy axial field for
all the short nominal sources it contains. Changing the arbitrary exterior
of an occupied signed mode only costs its rooted long-support tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedAxialExtension
open Finset Lattice Wilson RG Ac Marker QuadraticLocal Source Labels MSbar.Heath
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums Push.AbsoluteSums.Animals
open OPE.Therm WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side} {p : BudgetPoint} {V I T : Type} [DecidableEq V]
  {Γ : Census V} {o : V → Site n} (L : Lamps T I G p o Γ) {w : V → ℝ} {a D : ℝ}
  (hw : ∀ v,0 < w v) (ha : 0 ≤ a) (gross : Gross L w p.B a D)

private theorem long_bound {c tau f z : ℝ} (hp : 0 ≤ c) (tp : 0 ≤ tau)
    (small : ∀ x : ℂ, ‖x‖ ≤ f → c*tau*‖x‖ ≤ tau*f*z)
    (x y : ℂ) (hx : ‖x‖ ≤ f) (hy : ‖y‖ ≤ f) :
    c*tau*‖x-y‖ ≤ 2*(tau*f*z) := by
  calc
    _ ≤ c*tau*(‖x‖+‖y‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (mul_nonneg hp tp)
    _ = c*tau*‖x‖ + c*tau*‖y‖ := mul_add _ _ _
    _ ≤ _ := by linarith only [small x hx,small y hy]

private theorem sub_part (x y : Marker.Poly Γ) (s : Γ.Mode) :
    (x-y).part s = x.part s-y.part s := rfl

include hw ha gross in
theorem changed (t : T) (s : Γ.Mode) (v : V) (hv : v∈s.val) (b : ℕ) (U W : Config G n)
    (short : ∀ j,L.mode j = s → coverNumber p.B (L.ground j) < b →
      L.nominal t j U = L.nominal t j W) :
    Real.exp (a*b) * Poly.toll w s * ‖(bare L t U).part s - (bare L t W).part s‖ ≤ 2*D := by
  obtain ⟨f,hf,values,hit⟩ := gross.before
  let fee := Poly.toll w s
  let c := Real.exp (a*b)
  have fp : 0 ≤ fee := (Poly.worth hw _).le
  have cp : 0 ≤ c := Real.exp_nonneg _
  let weight (j : I) := if o v ∈ L.ground j then
    Poly.toll w (L.mode j)*f j*Real.exp (a*coverNumber p.B (L.ground j)) else 0
  have wallet := hit (o v)
  let y (U : Config G n) (j : I) := Poly.send (L.mode j) (L.nominal t j U)
  let e (j : I) := ((c*fee:ℝ):ℂ)*((y U j-y W j).part s)
  have scaled (x : ℂ) : ‖((c*fee:ℝ):ℂ)*x‖ = c*fee*‖x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg cp fp)]
  have row (j : I) : ‖e j‖ ≤ 2*weight j := by
    by_cases hm : s=L.mode j
    · have root : o v ∈ L.ground j := L.roots j v (hm ▸ hv)
      rw [show weight j = Poly.toll w s*f j*Real.exp (a*coverNumber p.B (L.ground j)) by
        simp only [weight,if_pos root,←hm]]
      simp only [e,scaled,y,sub_part,Poly.part_send,if_pos hm]
      by_cases little : coverNumber p.B (L.ground j) < b
      · rw [short j hm.symm little,sub_self,norm_zero,mul_zero]
        exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg fp (hf j)) (Real.exp_nonneg _))
      · have step : c ≤ Real.exp (a*coverNumber p.B (L.ground j)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.le_of_not_gt little)) ha)
        have bound (x : ℂ) (hx : ‖x‖ ≤ f j) :
            c*fee*‖x‖ ≤ fee*f j*Real.exp (a*coverNumber p.B (L.ground j)) := by
          calc
            _ = c*(fee*‖x‖) := mul_assoc _ _ _
            _ ≤ Real.exp (a*coverNumber p.B (L.ground j))*(fee*f j) :=
              mul_le_mul step (mul_le_mul_of_nonneg_left hx fp) (mul_nonneg fp (norm_nonneg _))
                (Real.exp_nonneg _)
            _ = _ := mul_comm _ _
        exact long_bound cp fp bound _ _ (values j t U) (values j t W)
    · simp only [e,y,sub_part,Poly.part_send,if_neg hm,sub_zero,mul_zero,norm_zero]
      exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (wallet.1 j)
  have weights : Summable (fun j => 2*weight j) := wallet.2.1.mul_left 2
  have finite := weights.of_nonneg_of_le (fun j => norm_nonneg (e j)) row
  have su := (WilsonRootedKioskCompleteFiling.sums L hw ha gross t U).1
  have sw := (WilsonRootedKioskCompleteFiling.sums L hw ha gross t W).1
  have outer : ((c*fee:ℝ):ℂ)*((bare L t U).part s-(bare L t W).part s) = ∑' j,e j := by
    rw [←sub_part,WilsonRootedKioskOccupiedSlip.bare,WilsonRootedKioskOccupiedSlip.bare,
      ←su.tsum_sub sw,Poly.share (su.sub sw),tsum_mul_left]
  have estimate := (norm_tsum_le_tsum_norm finite).trans (finite.tsum_le_tsum row weights)
  rw [←outer,scaled] at estimate
  exact estimate.trans ((tsum_mul_left.trans_le (mul_le_mul_of_nonneg_left wallet.2.2
    (by norm_num : 0≤(2:ℝ)))))

include hw ha gross in
/-- The same axial extension works for every admitted regular source in
the box. The exterior of U is arbitrary. -/
theorem locally (J : Voice G) (clear : Clear G J) (axes : Lattice.Order)
    (v : V) (b H : ℕ) (place : b*(4*p.B+2)+2*p.B < H) (room : 2*H<n.val)
    {τ r : ℝ} (weak : 0 ≤ τ) (rp : 0 < r) (U : Config G n)
    (cold : U ∈ House.chilly (WilsonAxialWindow.cells (o v) H) τ)
    (chart : (4*(H:ℝ)*Fintype.card PlaqAxes)*τ ≤ J.δ)
    (logarithm : J.C*((4*(H:ℝ)*Fintype.card PlaqAxes)*τ) ≤ r*p.threshold)
    (radius : r*p.threshold ≤ J.r) (stay : 4*J.C*r ≤ 1) :
    ∃ ξ : Directions G n,(∀ e, ‖ξ e‖ ≤ p.threshold) ∧ p.dirBound (o v) ξ ∧
      (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support n,Healthy p.threshold Y (increment 1 (z • ξ))) ∧
      ∀ (t : T) (s : Γ.Mode),v∈s.val →
        Real.exp (a*b)*Poly.toll w s*
          ‖(bare L t U).part s-(bare L t (increment 1 (r • ξ))).part s‖ ≤ 2*D := by
  obtain ⟨ξ,uniform,price,healthy,reads⟩ := WilsonRegisteredFlatLocal.bounded (p:=p) J clear axes (o v) H room
    τ r weak rp U cold chart logarithm radius stay
  refine ⟨ξ,uniform,price,healthy,?_⟩
  intro t s hv
  apply changed L hw ha gross t s v hv b U (increment 1 (r • ξ))
  intro j hm small
  apply reads (L.legal t j)
  intro x hx
  have loc := L.roots j v (hm ▸ hv)
  exact (Corona.extent _ p.B loc hx).trans_lt
    ((Nat.add_le_add_right (Nat.mul_le_mul_right _ small.le) _).trans_lt place)
end YM.Integration.WilsonReceivedAxialExtension
