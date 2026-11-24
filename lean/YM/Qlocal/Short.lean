import YM.Qlocal.Program
import YM.RGComparison01.Coin
/-!
# Cumulative price on ordinary *close* stretches. Use also with constant
 number of levels. Keeps relative ζ, does not overwrite with sum of 1 per
 step. Holder uses AFTER construction sorts, but demands paid up-front through
 increasing stages. This one NOT claiming sharper graph contraction or on the
 unrestricted spans (through which our realistic does NOT preserve original
 radii). Only reachable underwriting Lamp. Need engine.Mask updates lifts
 with stronger summands for path, reindex.Exception.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Program.Hull
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k' z n : ℕ} {δ r θ u v w E C : ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
open Camp
abbrev Y (x:Levels G):= x.clock.hatBeta
abbrev year (x:Levels G)(m:ℕ):= Real.log (x.clock.hatBeta m)
def Close (x:Levels G)(m j:ℕ) : Prop:= ((j-m:ℕ):ℝ) ≤ Real.sqrt (Real.sqrt (year x m))
section bound
variable (h:G.Simple)
lemma grown (M:Org.Metals G)(D:Rolls M.p)(A:Alloy M D) : Monotone (Y A.B.a):= monotone_nat_of_le_succ fun i=> by change _ ≤ A.B.a.clock.hatBeta (i+1); rw [PriceCompiler.beta_eq A.B.valid]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
private lemma hatP (A':Levels G)(m:ℕ):0 < Y A' m:=zero_lt_one.trans (A'.fits.delayed m)
lemma close_shrink (h:Close a m j)(hp:m ≤ n) : Close a n j:= le_trans (Nat.cast_le.mpr (show j-n ≤ j-m by omega)) (h.trans (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.log_le_log (hatP ..) (grown X D A hp)))))
include h
set_option maxHeartbeats 600000 in
lemma over_year : ∀ᶠ i in atTop, ∀ j≥i,Close a i j→ year a j ≤ 2*year a i:=by
 obtain ⟨m,hM⟩:= eventually_atTop.mp (Coin.neighboring_hats (a) h);
 let y:= Y a; let z:=year a; have hz : Tendsto z atTop atTop:= Real.tendsto_log_atTop.comp (Corrected.Grows.beta _ h)
 filter_upwards [eventually_ge_atTop m, hz.eventually_ge_atTop (1:ℝ)] with i ht hx j hi he;
 have hp : ∀ l:ℕ, y (i+l) ≤ 2^l*y i:= by
    intro n; induction n with
    | zero=> simp
    | succ l ih=> rw [pow_succ',mul_assoc _,← add_assoc]; exact le_trans (hM _ (by omega)) (mul_le_mul_of_nonneg_left ih (by norm_num))
 let ℓ := j-i; have hY : y j ≤ 2^ℓ*y i:= by convert hp ℓ using 2; omega
 have hL : Real.log (y j) ≤ (ℓ:ℝ)*Real.log 2+ Real.log (y i):= (Real.log_le_log (hatP ..) hY).trans_eq (by rw [Real.log_mul (by positivity) (hatP a i|>.ne'), Real.log_pow])
 have hw : Real.sqrt (year a i) ≤ year a i := by change 1≤year a i at hx; nlinarith [Real.sq_sqrt (zero_le_one.trans hx),Real.sqrt_nonneg (year a i)]
 have hV : (ℓ:ℝ) ≤ year a i:= he.trans (le_trans (Real.sqrt_le_sqrt hw) hw)
 change Real.log (y j) ≤ 2*Real.log (y i); refine hL.trans ?_; nlinarith only [hV,(by exact_mod_cast Nat.zero_le ℓ : 0 ≤ (ℓ:ℝ)), Real.log_two_lt_d9]
variable {η:ℕ→ℝ}{H T:ℕ→ℕ} (Q:Camp F η H T) -- vars not declared
set_option maxHeartbeats 1000000
lemma costs {b:ℝ}(k:ℕ)(hb:0 < b): ∀ᶠ i in atTop,∀ j≥i, Close a i j → (Q.scale i j)^k ≤ (Y a i)^b:= by
 let y:= Y a; let z:= fun i=> Real.sqrt (year a i); let w i:=Real.sqrt (z i); have hz:Tendsto z atTop atTop:= Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (Corrected.Grows.beta _ h)); have hv:Tendsto w atTop atTop:= Real.tendsto_sqrt_atTop.comp hz
 filter_upwards [over_year (A:=A) h,hv.eventually_ge_atTop (4*(k:ℝ)/b)] with i hi hl j hj he
 have hp:= hi j hj he; let u r:= Real.log (Q.step r)
 have hF k':0 < year a k':= Real.log_pos (A.B.a.fits.delayed _); have hQ k':0 < Q.step k':= zero_lt_one.trans_le (Q.fee k').1
 have hx (k':ℕ)(_ : i ≤ k')(hh:k' < j) : u k' ≤ 4*z i:= by
    have hε:= Real.log_le_log (hQ k') (Q.fee k' |>.2.1)
    let t:= (k'+1); have hy: year a t ≤ 2 *year a i:= (Real.log_le_log (hatP ..) (grown X D A hh)).trans hp
    rw [Real.log_pow, Scale.drawer, Real.log_exp, Nat.cast_ofNat] at hε; refine hε.trans ?_; change 2*z t ≤ 4*z i
    nlinarith only [hF i, Real.sq_sqrt (hF i).le,Real.sq_sqrt (hF t).le, Real.sqrt_nonneg (year a i),Real.sqrt_nonneg (year a t),hy]
 have hs:= (Finset.sum_le_sum (s:=Finset.Ico i j) (fun x (hh:x∈ Finset.Ico i j)=> hx _ (mem_Ico.mp hh).1 (mem_Ico.mp hh).2)); rw [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at hs
 rw [show Q.scale i j=∏ x∈Finset.Ico i j,Real.exp (u x) from prod_congr rfl (fun x hx=> (Real.exp_log (hQ x)).symm),← Real.exp_sum,← Real.exp_nat_mul, Real.rpow_def_of_pos (hatP ..)]; apply Real.exp_monotone
 refine le_trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k)) ?_
 have hl' : 4*(k:ℝ) ≤ w i*b:= (div_le_iff₀ hb).1 hl
 have ht : 0 ≤ z i := Real.sqrt_nonneg _; have hv: (w i)^2=z i:=Real.sq_sqrt ht; have hC: (z i)^2=Real.log (Y a i):= Real.sq_sqrt (hF i).le
 change (k:ℝ)*(((j-i:ℕ):ℝ)*(4*z i))≤ _
 calc
   _ ≤ (k:ℝ) * (w i * (4*z i)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (by positivity)) (Nat.cast_nonneg _)
   _ = (4*(k:ℝ)) * (w i * z i) := by ring
   _ ≤ (w i*b)*(w i*z i) := mul_le_mul_of_nonneg_right hl' (mul_nonneg (Real.sqrt_nonneg _) ht)
   _ = _ := by rw [← hC]; nth_rw 1 [show w i * b * (w i*z i)= (w i)^2*z i*b from (by ring)]; rw [hv]; ring
end bound
end YM.Qlocal.Program.Hull
