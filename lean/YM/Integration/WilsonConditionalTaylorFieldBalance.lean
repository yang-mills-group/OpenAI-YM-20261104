import YM.Integration.WilsonConditionalTaylorVacuumPrefix
import YM.Integration.WilsonConditionalTaylorResetCoordinates
import YM.Integration.WilsonKineticRebookingContinuity
import YM.Integration.WilsonConditionalTaylorKineticRebooking

/-! Comparison of *all* occupied field orders. Its only possible missing
coefficient is computed as the genuine zeroth field coefficient and spent
as the same spatially constant series in the incoming vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorFieldBalance
open Filter PowerSeries Lattice RG Wilson Precision Push.Uniform
open FormalBulk08 Orb Series Shore Lava MSbar MSbar.Cacao MSbar.Rolling MSbar.Midpoint
open WilsonConditionalTaylorResetCoordinates WilsonConditionalTaylorKineticRebooking
open scoped Classical Topology
variable {I : Type} [Fintype I] {m:ℕ}

def Fields (m : ℕ) (A B : Pap I) := ∀ e ≤ m, ∀ d,0<d →
  MvPolynomial.homogeneousComponent d (coeff e A)=MvPolynomial.homogeneousComponent d (coeff e B)

omit [Fintype I] in
theorem fromPrefix {A B : Pap I} (h : Through m A B) : Fields m A B :=
  fun e he d _ => congrArg (MvPolynomial.homogeneousComponent d) (h e he)

theorem account {A B : Pap I} (h : Fields m A B) (lowA : Kind A) (lowB : Kind B) :
    ∃ s : PowerSeries ℝ, coeff 0 s=0 ∧ Through m A (B+WilsonMovingVacuumConstant.scalar I s) := by
  let s : PowerSeries ℝ:=mk (fun e=>MvPolynomial.coeff 0 (coeff e A)-MvPolynomial.coeff 0 (coeff e B))
  refine ⟨s,by rw [show coeff 0 s=_ from coeff_mk ..,lowA,lowB,sub_self],?_⟩ 
  intro e he
  apply components
  intro d
  rw [map_add,WilsonMovingVacuumConstant.scalar,coeff_map,map_add]
  change _=MvPolynomial.homogeneousComponent d (coeff e B)+MvPolynomial.homogeneousComponent d (MvPolynomial.C (coeff e s))
  by_cases z : d=0
  · subst d
    simp only [MvPolynomial.homogeneousComponent_zero,MvPolynomial.coeff_C]
    rw [show coeff e s=_ from coeff_mk ..]
    simp only [if_true,map_sub]
    abel
  · rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_C _ _),if_neg z,add_zero]
    exact h e he d (by omega)

omit [Fintype I] in
theorem strip {A B : Pap I} (s : PowerSeries ℝ) (h : Through m A (B+WilsonMovingVacuumConstant.scalar I s)) :
    Fields m A B := by
  intro e he d pos
  rw [h e he,map_add,WilsonMovingVacuumConstant.scalar,coeff_map,map_add]
  change MvPolynomial.homogeneousComponent d (coeff e B)+MvPolynomial.homogeneousComponent d (MvPolynomial.C (coeff e s))=_
  rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_C _ _),if_neg pos.ne',add_zero]

theorem owes {G : Gauge} {n : Side} (v : G.Color) (Q : MvPolynomial (Primary n G) ℝ)
    {A B : Pap (Primary n G)} (h : Fields m A B) : Through m (primitive v A Q) (primitive v B Q) :=by
  intro e he
  unfold primitive
  simp only [map_sub,coeff_C_mul,projection,coeff_mk]
  rw [←WilsonConditionalTaylorKineticProjection.two v (coeff e A),h e he 2 (by decide),
    WilsonConditionalTaylorKineticProjection.two]

theorem clocks {A B : PowerSeries ℝ} (one : Wine.Fresh A) (one' : Wine.Fresh B) (h : Through m A B) :
    Through m (Wine.bookH A) (Wine.bookH B) ∧ Through m (Wine.bookU A) (Wine.bookU B) :=by
  have same (e : ℕ) (he : e ≤ m) : Tendsto (fun _ : ℕ=>coeff e A) atTop (𝓝 (coeff e B)):=by
    rw [h e he]
    exact tendsto_const_nhds
  exact ⟨fun e he=>tendsto_nhds_unique tendsto_const_nhds
    (WilsonKineticRebookingContinuity.forward m (fun _ : ℕ=>A) B (fun _=>one) one' same e he),
    fun e he=>tendsto_nhds_unique tendsto_const_nhds
    (WilsonKineticRebookingContinuity.inverse m (fun _ : ℕ=>A) B (fun _=>one) one' same e he)⟩

end YM.Integration.WilsonConditionalTaylorFieldBalance

