import YM.Integration.WilsonTrueProjectedSchool
import YM.Integration.WilsonRegisteredLogFare

/-! At a fixed physical reporting date the old registered source may have
a cutoff-dependent salary. The actual stage-column allowance and every
subcritical exponential in the upper mesh are erased by the original gate. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedUVBoundary
open Function Filter Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open MergeProof PhysicalNext.Repeat.Legato WilsonTrueProjectedDualHistory WilsonTrueProjectedCourse
open scoped Topology
variable {G : Gauge} (R : Run G)
local notation "𝓒" => R.family
local notation "A" => R.family.path.levels
local notation "s" => R.family.S.scale

theorem erased (simple : G.Simple)
    (slow : ∀j, ((R.family.S.block j).val : ℝ) ≤ Real.log (RG16.Lambda (A) j))
    (m : ℕ) {a C tol : ℝ} (subcritical : a < GermGraph.rate) (cap : 0 ≤ C) (target : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℝ, B ≤ C*Real.exp (a*s N) →
      Real.exp (-GermGraph.rate*(s N-s m))*((2+4*stock (𝓒) N)*B) ≤ tol := by
  let e := GermGraph.rate-a
  have he : 0 < e := sub_pos.mpr subcritical
  let t (n : ℕ) := e*s n
  have ht : Tendsto t atTop atTop := (𝓒).S.divergent.const_mul_atTop he
  have h0 : Tendsto (fun n => Real.exp (-(t n))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have h1 : Tendsto (fun n => t n*Real.exp (-(t n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht
  let D := 2+8*(A).clock.bar
  let E := 8*G.slopeConstant/e
  let K := C*Real.exp (GermGraph.rate*s m)
  have h := ((h0.const_mul D).add (h1.const_mul E)).const_mul K
  simp only [mul_zero,add_zero] at h
  obtain ⟨first,columns⟩ := eventually_atTop.mp (WilsonRegisteredLogFare.column R simple slow)
  filter_upwards [Filter.eventually_ge_atTop (first+1),h.eventually_le_const target] with N late small
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  intro B f
  have field := columns n (by omega)
  have hat : 0 ≤ (A).clock.hatBeta (n+1) := zero_le_one.trans ((A).fits.delayed (n+1)).le
  have bound : 2+4*stock (𝓒) (n+1) ≤ D+E*t (n+1) := by
    have wage := field.trans (mul_le_mul_of_nonneg_left (Real.log_le_self hat) (by norm_num : (0:ℝ) ≤ 2))
    change stock (𝓒) (n+1) ≤ 2*((A).clock.bar+G.slopeConstant*s (n+1)) at wage
    dsimp only [D,E,t]
    field_simp [ne_of_gt he]
    linarith only [wage]
  have positive : 0 ≤ 2+4*stock (𝓒) (n+1) := by
    have atLeast := (stage (𝓒) (n+1)).columns_ge
    change 1 ≤ stock (𝓒) (n+1) at atLeast
    linarith
  have times : Real.exp (-GermGraph.rate*(s (n+1)-s m))*Real.exp (a*s (n+1)) =
      Real.exp (GermGraph.rate*s m)*Real.exp (-t (n+1)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp only [e,t]
    ring
  calc
    _ ≤ Real.exp (-GermGraph.rate*(s (n+1)-s m))*((2+4*stock (𝓒) (n+1))*(C*Real.exp (a*s (n+1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left f positive) (Real.exp_pos _).le
    _ = K*((2+4*stock (𝓒) (n+1))*Real.exp (-t (n+1))) := by
      dsimp only [K]
      linear_combination C*(2+4*stock (𝓒) (n+1))*times
    _ ≤ K*((D+E*t (n+1))*Real.exp (-t (n+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bound (Real.exp_pos _).le)
        (mul_nonneg cap (Real.exp_pos _).le)
    _ = K*(D*Real.exp (-t (n+1))+E*(t (n+1)*Real.exp (-t (n+1)))) := by ring
    _ ≤ tol := small

theorem weaken {d N per j : ℕ} {Ψ : ∀ n, RG.Rep G ((𝓒).side n per)} {F : Spaces R per}
    {v : (𝓒).label d} {b B : ℝ} (paid : Full R (d:=d) (N:=N) Ψ F j v b) (raise : b ≤ B) :
    Full R (d:=d) (N:=N) Ψ F j v B := by
  obtain ⟨q,h,r,a,qr,pn,ha,price,balance⟩ := paid
  exact ⟨q,h,r,a,qr,pn,ha,price.trans raise,balance⟩

end YM.Integration.WilsonTrueProjectedUVBoundary
