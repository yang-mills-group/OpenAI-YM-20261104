import YM.Integration.WilsonPhysicalWindowCharges

/-! The fractional exponent of the original conditional Haar comparison on
every physical subinterval, including its terminal input error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWindowPosteriorPrice

open Filter Real Finset Lattice Wilson RG RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorMeshStops WilsonPhysicalWindowCharges
open scoped Topology BigOperators

variable {G : Gauge}

def step (C : Family G) (p : ℕ) (η : ℝ) (N n i : ℕ) : ℝ :=
  5*(C.path.levels.clock.hatBeta (i+1))^(-((p+1:ℕ):ℝ)/2) +
    2*(regulatorRun C N n (i+1))^((p:ℝ)+2-η)

private theorem bill0 (C : Family G) (q N n i : ℕ) : 0 ≤ bill C q N n i := by
  have temperature : 0 < C.path.levels.clock.hatBeta (i+1) :=
    zero_lt_one.trans (C.path.levels.fits.delayed _)
  have coupling : 0 ≤ regulatorRun C N n (i+1) := by unfold regulatorRun; positivity
  unfold bill
  positivity

theorem interval (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c : ℝ} (hc : c ≤ 2) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N n j t {η : ℝ}, η ≤ 1 → k ≤ j → j ≤ t →
      t ≤ ultraviolet R.family c k → ultraviolet R.family c k < N →
      (regulatorRun R.family N n (t+1))^((p:ℝ)+2-η) +
        ∑ i ∈ Finset.Ico j t, step R.family p η N n i ≤ ε*(regulatorRun R.family N n k)^p := by
  let C := R.family
  let u := ultraviolet C c
  have half : 0 < ε/2 := by linarith
  obtain ⟨b,hb⟩ := eventually_atTop.mp
    (WilsonDyadicReportingPrice.reserve (C:=C) hG R.makes 1 0 1 zero_le_one zero_lt_one)
  simp only [Real.rpow_zero,one_mul] at hb
  filter_upwards [eventually_ge_atTop b,summed R hG slow hc p half] with k hk money
  intro N n j t η hη kj jt tu live
  let g := regulatorRun C N n
  let f := bill C (p+1) N n
  have total := money N n live
  change (g (u k+1))^(p+1) + ∑ i ∈ Finset.Ico k (u k), f i ≤ ε/2*(g k)^p at total
  have positive (i : ℕ) (hi : i ≤ N) : 0 < g i := g_pos R.makes hi
  have contract (i : ℕ) (low : k ≤ i) (high : i ≤ N) :
      (g i)^((p:ℝ)+2-η) ≤ (g i)^(p+1) := by
    have upper : g i ≤ 1 := hb i (hk.trans low) n N high
    have order : ((p+1:ℕ):ℝ) ≤ (p:ℝ)+2-η := by push_cast; linarith
    exact (Real.rpow_le_rpow_of_exponent_ge (positive i high) upper order).trans_eq (Real.rpow_natCast _ _)
  have incl : Finset.Ico j t ⊆ Finset.Ico k (u k) := by
    intro i hi
    obtain ⟨lo,up⟩ := Finset.mem_Ico.mp hi
    exact Finset.mem_Ico.mpr ⟨kj.trans lo,up.trans_le tu⟩
  have original : (∑ i ∈ Finset.Ico j t, step C p η N n i) ≤ ∑ i ∈ Finset.Ico k (u k), f i := by
    refine (Finset.sum_le_sum (g:=f) ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg incl (fun i _ _=>bill0 C _ _ _ i))
    intro i hi
    obtain ⟨lo,up⟩ := Finset.mem_Ico.mp hi
    have paid := contract (i+1) (by omega) (by omega)
    unfold step
    change _ ≤ 5*(C.path.levels.clock.hatBeta (i+1))^(-((p+1:ℕ):ℝ)/2) + 2*(g (i+1))^(p+1)
    linarith only [paid]
  have sum0 : 0 ≤ ∑ i ∈ Finset.Ico k (u k), f i := Finset.sum_nonneg fun i _=>bill0 C _ _ _ i
  have head0 : 0 ≤ (g (u k+1))^(p+1) := pow_nonneg (positive _ live).le _
  have ending := contract (t+1) (by omega) (by omega)
  have head : (g (t+1))^(p+1) ≤ ε/2*(g k)^p := by
    rcases eq_or_lt_of_le tu with same | prior
    · rw [same]
      linarith only [sum0,total]
    · have inside : t ∈ Finset.Ico k (u k) := Finset.mem_Ico.mpr ⟨kj.trans jt,prior⟩
      have single := Finset.single_le_sum (f:=f) (fun i _=>bill0 C _ _ _ i) inside
      have β0 : 0 < C.path.levels.clock.hatBeta (t+1) := zero_lt_one.trans (C.path.levels.fits.delayed _)
      have therm := Real.rpow_nonneg β0.le (-((p+1:ℕ):ℝ)/2)
      have gg := pow_nonneg (positive (t+1) (by omega)).le (p+1)
      change 5*(C.path.levels.clock.hatBeta (t+1))^(-((p+1:ℕ):ℝ)/2) + 2*(g (t+1))^(p+1) ≤ _ at single
      linarith only [therm,gg,single,head0,total]
  change (g (t+1))^((p:ℝ)+2-η) + (∑ i ∈ Finset.Ico j t, step C p η N n i) ≤ ε*(g k)^p
  linarith only [ending,head,original,head0,total]

end YM.Integration.WilsonPhysicalWindowPosteriorPrice

