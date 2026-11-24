import YM.QuadraticLocal.Vacuum.Recover
import YM.QuadraticLocal.Vacuum.Captain
/-!
# One rooted ALL-ORDER hit budget with the arbitrary-E price
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
local notation "D"=> grow G L s
variable (N : Captain H j C' d v Y A b r B q k χ) (hd : 1 ≤ grow G L s) {π:ℕ} {τ:Multiplier} (hh : Lions τ π N.conduit)
variable (n : ℕ) (ht : Armada Q L μ a s i B j k)
variable (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
variable (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)
open YM.AllOrder.Burn
variable {M:Set ℕ} (hl:Lions τ (alt ℓ) N.conduit)
include hd ht hl hs hp
lemma chargedHit (w:ℝ) (hw:1≤w)(hy:∀ i, i∉M→ w≤τ.weight i)
    (hc : D^alt ℓ ≤ Real.exp (Q.mark L μ s)) (hx : D^alt ℓ≤Real.exp (Q.ε*Pressure.Stores.till s)) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>if tiredT H (typeT M ℓ) (alt ℓ) z then N.markΦ z n else 0) a
        (((D^alt ℓ)⁻¹+(D^3*w)⁻¹)*(collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  intro x
  let e:=( (D^alt ℓ)⁻¹+(D^3*w)⁻¹ ); have he:= zero_lt_one.trans_le hd; have hf:= zero_lt_one.trans_le hw; have hs' : 0≤ e:=by unfold e; positivity
  have hy':=budget_scale hs' (masterHit N hd hl n ht hs hp x)
  let z:= D^alt ℓ; let χ:= D^3*w
  have hz:0<z:=by unfold z; positivity
  have hcc:0<χ:=by unfold χ; positivity
  have ht {A k:ℝ} (h:0 ≤ A)(he': z ≤ k ∨ χ ≤ k) : A ≤ e*(k*A):= by
      let Y:=min z χ; have hY:0<Y:=lt_min hz hcc; have hA: Y≤k:= he'.elim (fun h=> (min_le_left ..).trans h) (fun h=> (min_le_right ..).trans h)
      rw [←mul_assoc]; refine le_mul_of_one_le_left h (le_trans ?_ (mul_le_mul_of_nonneg_left hA hs'))
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (show Y⁻¹ ≤ e from ?_) hY.le); · rw [inv_mul_cancel₀ hY.ne']
      rcases le_total z χ with H | H
      · rw [show Y=z from min_eq_left H]; exact le_add_of_nonneg_right (inv_nonneg.mpr hcc.le)
      · rw [show Y=χ from min_eq_right H]; exact le_add_of_nonneg_left (inv_nonneg.mpr hz.le)
  have hw'(z:H.fragrances):0 ≤ N.markΦ z n:= mul_nonneg (pow_nonneg (by unfold shiftG; positivity) _) (N.pvc _)
  refine budget_mono hy' (fun z=>?_) (fun z=>?_)
  · dsimp only; split_ifs
    next => exact mul_nonneg (hw' _) (Real.exp_pos _).le
    next => simp
    exact le_rfl
  dsimp only; split
  next ht' =>
      split
      next h => rw [mul_assoc]; exact ht (mul_nonneg (hw' _) (Real.exp_pos _).le) (earnsW_low τ hd w hw hy z h hc hx)
      next h => rw [zero_mul]; simpa only [if_pos ht'] using hy'.1 z
  rw [mul_zero]
end YM.PhysicalNext.Repeat.Height
