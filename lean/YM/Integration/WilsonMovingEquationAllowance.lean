import YM.Integration.WilsonMovingReportTreasury
import YM.Integration.WilsonReportDiscrepancyCopies

/-! One presold marker allowance pays the entire true thermal port, the
original fly reciprocal, and the cutoff supremum. Its adjacent invoice is
uniform even though the minimizing RG16 port may change at the next scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingEquationAllowance
open Filter Set Lattice RG RG16 RG16.Literal OPE MergeProof Accent
open WilsonCutoffDiscrepancyPrice WilsonSignedReportPrice
open scoped BigOperators Topology
variable {G : Gauge} (C : Family G)

theorem regularize (f : ℕ → ℝ) (h : FullVolume.Sluggish C (fun i=> f i.1)) :
    FullVolume.Sluggish C (fun i => room C f i.1) := by
  intro δ hd
  obtain ⟨K,hK,hp⟩:=presold C f h (half_pos hd)
  have hgrow := Real.tendsto_exp_atTop.comp (C.S.divergent.const_mul_atTop (half_pos hd))
  apply FullVolume.late.mpr
  filter_upwards [hgrow.eventually_ge_atTop K] with k hk p
  change ‖room C f k‖ ≤ Real.exp (δ*C.S.scale k)
  rw [Real.norm_of_nonneg (zero_le_one.trans (heard C f h k).1)]
  apply (hp k).trans
  apply (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le).trans_eq
  change Real.exp (δ/2*C.S.scale k)*Real.exp (δ/2*C.S.scale k)=_
  rw [← Real.exp_add]; congr 1; ring

def fare (d : ℕ) {L : ℝ} (B : ℝ) (hL : 0<L) (E : ℕ → ℝ) (k : ℕ) :=
    stakes C (port C L B hL k) k * marker C d k * room C E k

theorem funded (hG : G.Simple) (Y : Therm.Poetry C.path.levels)
    (pace : ∀ k, ((C.S.block k).val:ℝ) ≤ Real.log (Lambda C.path.levels k))
    (d : ℕ) {L B : ℝ} (hL : 0<L) (hB : 0<B) (E : ℕ → ℝ)
    (hE : FullVolume.Sluggish C (fun i=>E i.1)) :
    FullVolume.Sluggish C (fun i=>fare C d B hL E i.1) := by
  have hs : FullVolume.Sluggish C (fun i => stakes C (port C L B hL i.1) i.1) := by
    intro δ hd
    apply FullVolume.late.mpr
    filter_upwards [WilsonMovingReportTreasury.posted C hG Y hL hB pace hd] with k hk p
    change ‖stakes C (port C L B hL k) k‖ ≤ Real.exp (δ*C.S.scale k)
    rw [Real.norm_of_nonneg (show 0 ≤ stakes C (port C L B hL k) k from (Real.exp_pos _).le)]
    exact hk
  exact (hs.mul (marker_paid C hG d)).mul (regularize C E hE)

/-- Eqs. T29668–80: a *single* numerical radius for a finite set of
alternatives in a physical slot. Independently paid top prices may be
included among these actual scalar rows. -/
theorem alternatives {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i∈s, FullVolume.Sluggish C (fun j=>f i j.1))
    (pace : ∀ k, ((C.S.block k).val:ℝ) ≤ Real.log (Lambda C.path.levels k))
    (hG : G.Simple) :
    ∃ A : ℕ → ℝ, Monotone A ∧ (∀ k, 1 ≤ A k ∧ (∑ i∈s, |f i k|) ≤ A k) ∧
      (∀ δ>0, ∃ K:ℝ, 1≤K ∧ ∀ k, A k≤K*Real.exp (δ*C.S.scale k)) ∧
      ∀ q:ℕ, ∀ δ>0, ∀ᶠ k in atTop,
        (A (k+1)/A k)^q ≤ Real.exp (δ*(C.path.levels.clock.coverSize k:ℝ)) := by
  let X (k : ℕ) := ∑ i∈s, |f i k|
  have hX : FullVolume.Sluggish C (fun j => X j.1) :=
    FullVolume.Sluggish.sum s (fun i j=>|f i j.1|) (fun i hi => (hf i hi).norm)
  refine ⟨room C X,WilsonReportDiscrepancyCopies.monotone C X hX,fun k => ?_,
    fun _ hd => presold C X hX hd,fun q _ hd => WilsonReportDiscrepancyCopies.grade C hG X hX pace q hd⟩
  have hx := (heard C X hX k).2 k
  rw [price,sub_self,max_self,mul_zero,Real.exp_zero,mul_one,
    abs_of_nonneg (show 0≤X k from Finset.sum_nonneg (fun _ _=>abs_nonneg _))] at hx
  exact ⟨(heard C X hX k).1,hx⟩

end YM.Integration.WilsonMovingEquationAllowance
