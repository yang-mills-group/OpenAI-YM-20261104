import YM.Integration.WilsonRetainedJointVertexMarked

/-! The simultaneous product of the complete separately priced site sources
uses one more Hölder slot for an arbitrary correlated marked polynomial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open MeasureTheory Finset
open scoped BigOperators Classical

private theorem roster_scalar (K n : ℕ) {g ε η : ℝ} (gp : 0<g) (ep : 0<ε) :
    let k:=min 1 ε/(2:ℝ)^(n+2)
    let u:=η/((n:ℝ)+1)
    (2:ℝ)^(n+2)*g^K*(k*g^(3-u))^(n+1)≤ε*g^(((K+3*(n+1):ℕ):ℝ)-η) := by
  intro k u
  have positive : 0≤k:=div_nonneg (le_min zero_le_one ep.le) (by positivity)
  have small : k≤1:=by
    apply (div_le_one (by positivity)).2
    exact (min_le_left 1 ε).trans (one_le_pow₀ (by norm_num))
  have tiny : k^(n+1)≤k:=by
    rw [pow_succ]
    exact mul_le_of_le_one_left positive (pow_le_one₀ positive small)
  have coins : (2:ℝ)^(n+2)*k^(n+1)≤ε:=by
    calc _ ≤ (2:ℝ)^(n+2)*k:=mul_le_mul_of_nonneg_left tiny (by positivity)
      _ = min 1 ε:=by dsimp only [k]; field_simp
      _ ≤ ε:=min_le_right .. 
  have units : g^K*(g^(3-u))^(n+1)=g^(((K+3*(n+1):ℕ):ℝ)-η):=by
    rw [←Real.rpow_natCast g K,←Real.rpow_natCast (g^(3-u)) (n+1),←Real.rpow_mul gp.le,←Real.rpow_add gp]
    congr 1
    dsimp only [u]
    push_cast
    field_simp
    ring
  rw [mul_pow,←units]
  calc _ = ((2:ℝ)^(n+2)*k^(n+1))*(g^K*(g^(3-u))^(n+1)):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right coins (mul_nonneg (pow_nonneg gp.le _) (pow_nonneg (Real.rpow_nonneg gp.le _) _))

theorem roster_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n K : ℕ)
    {g η ε : ℝ} (gp : 0<g) (gs : g≤1) (ep : 0<ε) (a t : Fin (n+1)→Ω→ℂ) :
    let k:=min 1 ε/(2:ℝ)^(n+2)
    let u:=η/((n:ℝ)+1)
    (∀ i,Integrable (a i) μ ∧ Integrable (fun z=>‖a i z‖^(n+2)) μ ∧
      (∫ z,‖a i z‖^(n+2) ∂μ)≤(k*g^(3-u))^(n+2)) →
    (∀ i,Integrable (fun z=>a i z-t i z) μ ∧ Integrable (fun z=>‖a i z-t i z‖^(n+2)) μ ∧
      (∫ z,‖a i z-t i z‖^(n+2) ∂μ)≤(k*g^(((K+3:ℕ):ℝ)-u))^(n+2)) →
    ∀ (J : Ω→ℂ) {B : ℝ}, 0≤B → AEStronglyMeasurable J μ →
    (Integrable (fun z=>‖J z‖^(n+2)) μ ∧ (∫ z,‖J z‖^(n+2) ∂μ)≤B^(n+2)) →
    let E:=fun z=>J z*((∏ i,t i z)-∏ i,a i z)
    Integrable E μ ∧ ‖∫ z,E z ∂μ‖≤B*(ε*g^(((K+3*(n+1):ℕ):ℝ)-η)) := by
  intro k u actual error J B B0 jm marked E
  let base:=k*g^(3-u)
  let more:=k*g^(((K+3:ℕ):ℝ)-u)
  have k0 : 0≤k:=div_nonneg (le_min zero_le_one ep.le) (by positivity)
  have same : more=g^K*base:=by
    dsimp only [base,more]
    rw [mul_left_comm (g^K),←Real.rpow_natCast g K,←Real.rpow_add gp]
    congr 2
    push_cast
    ring
  have mt (i) : AEStronglyMeasurable (t i) μ:=by
    have h:=(actual i).1.aestronglyMeasurable.sub (error i).1.aestronglyMeasurable
    simpa only [Pi.sub_def,sub_sub_cancel] using h
  have incoming (i : Fin (n+1)) : Integrable (fun z=>‖a i z‖^(Fintype.card (Fin (n+1))+1)) μ ∧
      (∫ z,‖a i z‖^(Fintype.card (Fin (n+1))+1) ∂μ)≤base^(Fintype.card (Fin (n+1))+1):=by
    simpa only [Fintype.card_fin] using (actual i).2
  have changed (i : Fin (n+1)) : Integrable (fun z=>‖t i z-a i z‖^(Fintype.card (Fin (n+1))+1)) μ ∧
      (∫ z,‖t i z-a i z‖^(Fintype.card (Fin (n+1))+1) ∂μ) ≤ more^(Fintype.card (Fin (n+1))+1):=by
    simp_rw [Fintype.card_fin,norm_sub_rev (t i _) (a i _)]
    exact (error i).2
  obtain ⟨int,bill⟩:=joined_marked_price μ a t (fun _=>base) (fun _=>more) (fun _=>base)
    (fun i=>(actual i).1.aestronglyMeasurable) mt (fun _=>mul_nonneg k0 (Real.rpow_nonneg gp.le _))
    (fun _=>mul_nonneg k0 (Real.rpow_nonneg gp.le _)) incoming changed
    (pow_nonneg gp.le K) (pow_le_one₀ gp.le gs) (fun _=>le_rfl) (fun _=>same.le)
    J jm B0 (by simpa only [Fintype.card_fin] using marked)
  refine ⟨int,bill.trans (mul_le_mul_of_nonneg_left ?_ B0)⟩
  simpa only [prod_const,card_univ,Fintype.card_fin,base,k,u] using roster_scalar K n (η:=η) gp ep

end YM.Integration.OriginalMarkedRunAction
