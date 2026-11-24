import YM.FullVolume.Cross
import YM.FullVolume.Sluggish
import YM.OPE.Height

/-! The Wilson cutoff price of a signed discrepancy at a *moving* report.
The room is positive and monotone, includes the exact top price, and controls
each adjacent ratio. No spacetime placements enter this scalar purchase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCutoffDiscrepancyPrice

open Filter Set Finset Lattice Push.RelayDifference
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G) (E : ℕ → ℝ)

def price (k N : ℕ) : ℝ :=
  |E N| * Real.exp (-gamma * max 0 (C.S.scale N - C.S.scale k))

def room (k : ℕ) : ℝ := sSup (insert 1 (Set.range (price C E k)))

private theorem scale_pos (m : ℕ) : 0 ≤ C.S.scale m :=
  C.S.scale_zero.symm.le.trans ((OPE.scale_mono C.S).monotone (Nat.zero_le m))

private theorem global (hE : FullVolume.Sluggish C (fun i => E i.1))
    {δ : ℝ} (hd : 0 < δ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ N, |E N| ≤ K * Real.exp (δ*C.S.scale N) := by
  obtain ⟨n,hn⟩ := eventually_atTop.mp (FullVolume.late.mp (hE δ hd))
  let K : ℝ := 1 + ∑ i ∈ range n, |E i|
  have hK : 1 ≤ K := le_add_of_nonneg_right (sum_nonneg fun i _ => abs_nonneg (E i))
  refine ⟨K,hK,fun N => ?_⟩
  by_cases hN : N < n
  · have h₁ := single_le_sum (f := fun i => |E i|) (fun i _ => abs_nonneg (E i))
      (mem_range.mpr hN)
    exact (h₁.trans (le_add_of_nonneg_left zero_le_one)).trans
      (le_mul_of_one_le_right (zero_le_one.trans hK)
        (Real.one_le_exp (mul_nonneg hd.le (scale_pos C N))))
  · exact (hn N (Nat.le_of_not_gt hN) 0).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le hK)

theorem discounted (hE : FullVolume.Sluggish C (fun i => E i.1))
    {δ : ℝ} (hd : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k N, k ≤ N →
      |E N| * Real.exp (-gamma*(C.S.scale N-C.S.scale k)) ≤
        K * Real.exp (δ*C.S.scale k) *
          Real.exp (-(gamma-δ)*(C.S.scale N-C.S.scale k)) := by
  obtain ⟨K,hK,hi⟩ := global C E hE hd
  refine ⟨K,hK,fun k N _ => ?_⟩
  calc
    _ ≤ (K*Real.exp (δ*C.S.scale N))*Real.exp (-gamma*(C.S.scale N-C.S.scale k)) :=
      mul_le_mul_of_nonneg_right (hi N) (Real.exp_pos _).le
    _ = _ := by simp only [mul_assoc,← Real.exp_add]; congr 2; ring

private theorem bounded (hE : FullVolume.Sluggish C (fun i => E i.1))
    {δ : ℝ} (hd : 0 < δ) (hg : δ ≤ gamma) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k N, price C E k N ≤ K * Real.exp (δ*C.S.scale k) := by
  obtain ⟨K,hK,hN⟩ := global C E hE hd
  refine ⟨K,hK,fun k N => ?_⟩
  calc
    price C E k N ≤ (K*Real.exp (δ*C.S.scale N))*
        Real.exp (-gamma*max 0 (C.S.scale N-C.S.scale k)) :=
      mul_le_mul_of_nonneg_right (hN N) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_assoc,← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_left (le_max_right 0 (C.S.scale N-C.S.scale k)) hd.le
      have h₂ := mul_le_mul_of_nonneg_right hg (le_max_left 0 (C.S.scale N-C.S.scale k))
      linarith

theorem presold (hE : FullVolume.Sluggish C (fun i => E i.1)) {δ : ℝ}
    (hd : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k, room C E k ≤ K*Real.exp (δ*C.S.scale k) := by
  have hg : 0 < gamma := by norm_num [gamma]
  obtain ⟨K,hK,hN⟩ := bounded C E hE (lt_min hd hg) (min_le_right δ gamma)
  refine ⟨K,hK,fun k => csSup_le ⟨1,mem_insert ..⟩ ?_⟩
  intro s hs
  rcases hs with hs | ⟨N,rfl⟩
  · rw [hs]
    exact hK.trans (le_mul_of_one_le_right (zero_le_one.trans hK)
      (Real.one_le_exp (mul_nonneg hd.le (scale_pos C k))))
  · exact (hN k N).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (min_le_left δ gamma) (scale_pos C k))) (zero_le_one.trans hK))

private theorem bound (hE : FullVolume.Sluggish C (fun i => E i.1)) (k : ℕ) :
    BddAbove (insert 1 (Set.range (price C E k))) := by
  obtain ⟨K,hK,h⟩ := bounded C E hE (by norm_num [gamma] : 0 < gamma) le_rfl
  refine ⟨max 1 (K*Real.exp (gamma*C.S.scale k)),fun s hs => ?_⟩
  rcases hs with hs|⟨N,rfl⟩
  · rw [hs]; exact le_max_left .. 
  · exact (h k N).trans (le_max_right ..)

theorem heard (hE : FullVolume.Sluggish C (fun i => E i.1)) (k : ℕ) :
    1 ≤ room C E k ∧ ∀ N, price C E k N ≤ room C E k :=
  ⟨le_csSup (bound C E hE k) (mem_insert ..),fun N =>
    le_csSup (bound C E hE k) (mem_insert_of_mem _ ⟨N,rfl⟩)⟩

theorem adjacent (hE : FullVolume.Sluggish C (fun i => E i.1)) (k : ℕ) :
    room C E (k+1) ≤ room C E k * Real.exp (gamma*Real.log (C.S.block k).val) := by
  have hr := heard C E hE k
  have hx : 0 ≤ Real.log (C.S.block k).val := Real.log_nonneg (by exact_mod_cast (C.S.block k).pos)
  have hg : 0 ≤ gamma := by norm_num [gamma]
  apply csSup_le ⟨1,mem_insert ..⟩
  intro s hs
  rcases hs with hs|⟨N,rfl⟩
  · rw [hs]
    exact hr.1.trans (le_mul_of_one_le_right (zero_le_one.trans hr.1)
      (Real.one_le_exp (mul_nonneg hg hx)))
  · apply le_trans _ (mul_le_mul_of_nonneg_right (hr.2 N) (Real.exp_pos _).le)
    unfold price
    rw [mul_assoc,← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    rw [C.S.scale_succ]
    have h₁ : max 0 (C.S.scale N - C.S.scale k) ≤
        max 0 (C.S.scale N - (C.S.scale k+Real.log (C.S.block k).val))+
          Real.log (C.S.block k).val := by
      apply max_le (add_nonneg (le_max_left ..) hx)
      linarith only [le_max_right 0 (C.S.scale N-(C.S.scale k+Real.log (C.S.block k).val))]
    linarith only [mul_le_mul_of_nonneg_left h₁ hg]

end YM.Integration.WilsonCutoffDiscrepancyPrice
