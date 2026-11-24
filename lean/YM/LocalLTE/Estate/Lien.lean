import YM.LocalLTE.Crafts.Bands
import YM.LocalLTE.Newborn.Contract
import YM.LocalLTE.Estate.Choir
import YM.LocalLTE.Pool.Dawn
import YM.LocalLTE.Bonnet.Canopy
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
variable {p:ℕ}(W:Trail H p)(M:Preview H)(v:Bolt A)(hv:Made H W M v)
open Progress.DirectedRecipe Averaging LocalLTE.FrameBox Price
section generic
variable {G:Gauge}{n:Side} (R:Rep G n) (f:ℕ→ℕ)(ϕ:ℕ→ Config G n→ℝ) (j:ℕ){k t:ℝ} {m:ℕ}(hL:Coup.License j R k t f m) {v e μ:ℝ}
-- preserve same Supports.K.H actual. mark estimates at full history separately.
def charged (D:Activities G n)(f:ℕ→ Config G n→ℝ) := {D with E:=f}
variable (h:∀ i,ϕ i=if f i≤ j then R.activities.E i else 0)(ht:1 ≤ t)
local notation "p'"=>R.p
variable (hJ:R.activities.Valid R.p v μ) (hx:∀ s b,∃ V:R.activities.Moves s b,∀ i,f (V.ep i)=f i)
include hL h hJ ht hx
lemma components : (charged R.activities ϕ).Valid R.p v μ ∧ (charged R.activities (R.activities.E-ϕ)).Valid R.p (t^(Pastel.chip (j+1))) μ:=by
    let A':= charged R.activities ϕ; let B':= charged R.activities (R.activities.E-ϕ)
    let A:=R.activities
    have hr :B'.E= fun i=> if f i≤ j then 0 else A.E i:= by unfold B' charged; funext i; simp only [Pi.sub_apply]; rw [h]; split; rw [sub_self]; exact sub_zero _
    have hi (i:ℕ): Comic G (A.reg i) (p') (A'.E i) ∧ Comic G (A.reg i) (p') (B'.E i):=by
       have he: Comic G (A.reg i) R.p (A.E i):= ⟨hJ.regular.smooth i,hJ.regular.at_flat i,hJ.regular.vanish i⟩
       rw [show A'.E i=ϕ i from rfl,h i,hr]; dsimp only; split; exact ⟨he,Price.flick _⟩; exact ⟨Price.flick _,he⟩
    have ht' (s:Signed)(b: Site n): Nonempty (A'.Moves s b) ∧ Nonempty (B'.Moves s b):=by
       obtain ⟨M,hM⟩:= hx s b
       refine ⟨⟨⟨M.ep,M.kp, M.reg_site,M.reg_support, M.forced_support, M.forced_inventory,M.forced_tests,?_, M.valuesK⟩⟩,⟨⟨M.ep,M.kp,M.reg_site,M.reg_support,M.forced_support,M.forced_inventory,M.forced_tests,?_,M.valuesK⟩⟩⟩
       · intro i U; change ϕ (M.ep i) U=ϕ i (pull _ _ _); rw [h,h,hM]; split; exact M.valuesE ..; rfl
       intro i U; rw [hr]; dsimp only; rw [hM]; split; rfl; exact M.valuesE ..
    have hf (f:ℕ→ Config G n→ℝ): (charged A f).ForcedFamily (p'):= by obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩:= hJ.forced; exact ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩
    obtain ⟨hP,u,hK,hX⟩:=hL.bills
    refine ⟨⟨⟨fun i=>(hi i).1.1,fun i=>(hi i).1.2.1,fun i=>(hi i).1.2.2⟩,hf _,fun p v=> (ht' p v).1,?_,hJ.boundK⟩, ⟨⟨fun i=>(hi i).2.1,fun i=>(hi i).2.2.1,fun i=>(hi i).2.2.2⟩,hf _,fun p v=> (ht' p v).2,?_,hJ.boundK⟩⟩
    · obtain ⟨v,hq,hV⟩:= hJ.boundE; refine ⟨v,fun i=>?_,hV⟩
      change R.p.supBounds _ _ (ϕ i) _; rw [h]; split; exact hq i; exact VerifiedReset.sup_le (WilsonStartup.Start.zero_bound) (hq i|>.1)
    let d i:= if f i≤j then 0 else u i; have hxG:0 < t:=zero_lt_one.trans_le ht; let b:=bloom t (j+1); have hB:0<b:= zero_lt_one.trans_le (bloom_bill ht _); let a:=Pastel.chip
    refine ⟨d,fun i=>?_,fun i=>budget_loosen (budget_mono (budget_scale (inv_pos.mpr hB|>.le) (hX i)) (fun i=>?_) (fun i=> ?_)) ?_⟩
    · change R.p.supBounds _ _ (B'.E i) _; rw [hr]; dsimp only; unfold d; split; exact WilsonStartup.Start.zero_bound; exact hK i
    · split; next h=> exact mul_nonneg (Real.exp_nonneg _) (by unfold d; split; exact le_rfl; exact (hK _).1)
      exact le_rfl
    · change (if (A.reg i).site=_ then R.p.mass _ _ else 0) ≤ (b⁻¹* _); split
      next h=>
         dsimp only; unfold d; split
         next h=> unfold BudgetPoint.mass; rw [mul_zero]; exact mul_nonneg (inv_pos.mpr hB|>.le) (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (zero_le_one.trans (hP _)) (hK _ |>.1)))
         next ht'=> unfold BudgetPoint.mass; rw [← div_eq_inv_mul, le_div_iff₀ hB, mul_assoc]; exact mul_le_mul_of_nonneg_left ((mul_comm (u i) _).trans_le (mul_le_mul_of_nonneg_right (East.bloom_rise ht _ (show j < f i from not_le.mp ht')) (hK _|>.1))) (Real.exp_nonneg _)
      next h=> rw [mul_zero]
    exact (Eq.le (by rw [← div_eq_inv_mul, Coup.chip_zero,← East.bloom_price (j+1) t hxG]; rw [div_eq_iff hB.ne']; exact mul_comm b _)) -- syntax unfold goal
end generic
end YM.PhysicalNext.Repeat.Mallow
