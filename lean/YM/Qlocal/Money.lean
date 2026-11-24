import YM.Qlocal.Short
import YM.Qlocal.Continuing
/-!
# All finite coupling powers in the strong rough K estimate.

 Even after dividing by the ACTUAL κ, on CLOSE structures, all fields.
 Revenue has no number-of-markers interpretation alone; marker recovery cost
 reflects the disjoint max allowed degree. Independent roots/moves need separate tickets.
 strong K forecast -> strong rents before division. `p_i^geo` through each step
 as in BaubleDesk; accumulation of radii does NOT restore arbitrarily many copies or unlimited
 steps, hence preserve un-recovered version and specify the size of the interval explicitly.
 Any better strong norm from the actual λ-loop can compete independently. δ outfits relative prices and
 disjoint-normalizations. Does not infer matching of any analytic insertion inputs here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Program
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe ConnectedActivityE6 Coat PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k' z n : ℕ} {δ r θ u v w E C ℓ: ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
open Camp Frigus Time
namespace Hull
abbrev fineY (A:Levels G)(i:ℕ):= A.clock.hatBeta (i+1)
abbrev hard (A:Levels G)(i:ℕ):= A.clock.forcedAllowance i
def divisor (A:Levels G)(i:ℕ):= Real.sqrt (hard A i)
lemma luminous (A:Levels G)(i:ℕ): 0 < divisor A i ∧ divisor A i ≤ 1∧hard A i=divisor A i* divisor A i:= ⟨Real.sqrt_pos.mpr (reserve_bounds ..).1,(Real.sqrt_le_sqrt (reserve_bounds A i).2).trans (le_of_eq (Real.sqrt_one)),(Real.mul_self_sqrt (reserve_bounds ..).1.le).symm⟩
-- Avoid issue derivative. gStep β notation.A.*.
lemma blue (h: θ∈ band a n) : 1 < Hull.Y a n ∧ 0 < θ∧ 0 < gStep θ∧ (gStep θ)^2=θ⁻¹ := by
 let y:= (a).clock.hatBeta n; have hz: 0<θ := (half_pos (zero_lt_one.trans (A.B.a.fits.delayed n))).trans_le (show y/2 ≤ θ from h.1); refine ⟨A.B.a.fits.delayed n,hz, inv_pos.mpr (Real.sqrt_pos.mpr hz),?_⟩; unfold gStep; rw [inv_pow,Real.sq_sqrt hz.le]
-- strength of acknowledgment any powers T deep. lost factors.B.Require ξ.
-- `Pays'` after any close output with any β≥ threshold. Use comparator constants to target δ. prove gamma scale ≤ 2*g^(-ε). `(hat)^(ε/2)`, multiply. when accumulating reading use β actual step.D.Prop.
variable {η:ℕ→ℝ}{H T:ℕ→ℕ}(K:Camp F η H T)
def soft (ρ β: ℝ):= (2:ℝ)^(ρ/2)*gStep β^(-ρ) -- >1 eventually along actual.
lemma looming (h:G.Simple)(hq : 0<δ) (r:ℕ) : ∀ᶠ m in atTop,∀ j≥m, Close a m j →∀ β∈band a (m+1), (K.scale m j)^r ≤ soft δ β:= by
 filter_upwards [costs F h K r (half_pos hq)] with m hm j hj hr β hβ
 let x:= Y a m; let y:= Y a (m+1); obtain ⟨ht,hv,hg,hq'⟩:= blue (A:=A) hβ; have hH : x≤y:= grown X D A m.le_succ; have hp : y ≤ 2*β:= by linarith only [show y/2 ≤ β from hβ.1]
 apply (hm j hj hr).trans; apply (Real.rpow_le_rpow (show 0 ≤ x from zero_le_one.trans (A.B.a.fits.delayed m).le) (hH.trans hp) (half_pos hq).le).trans_eq; rw [Real.mul_rpow (by norm_num : (0:ℝ)≤ 2) hv.le]; unfold soft; congr 1
 rw [Real.rpow_neg hg.le]; conv_lhs => rw [show β=(gStep β)^(-2:ℝ) from (by rw [Real.rpow_neg hg.le,Real.rpow_two,hq',inv_inv])]
 rw [← Real.rpow_mul hg.le,← Real.rpow_neg hg.le]; ring_nf

lemma bagged (h:G.Simple)(hi:Tendsto T atTop atTop) (k v:ℕ) : ∀ᶠ m in atTop,∀ j≥m, Close a m j →∀ β∈band a (m+1), (K.scale m j)^k*hardcap a T m ≤ hard a m * gStep β^v:=by
 -- keep h stage.E.Body. use monitor high T, pay arbitrary post rank charges ≤1 globally.
 let S := a; let y:= Y a; let x t:= fineY a t; have hx : Tendsto x atTop atTop:= (Corrected.Grows.beta a h).comp (tendsto_add_atTop_nat 1)
 have hA: Tendsto (fun i=> T (A.B.a.clock.J (i+1))) atTop atTop:= hi.comp ((A.B.a.fits.deep).comp (tendsto_add_atTop_nat 1))
 filter_upwards [costs F h K k zero_lt_one,hA.eventually_ge_atTop (v+1), hx.eventually_ge_atTop 2] with m hm hz hx j hj hr β hβ
 have he : (K.scale m j)^k ≤ x m:= (hm j hj hr).trans ((Real.rpow_one (Y a m)).trans_le (grown X D A m.le_succ)); let p:=K.scale m j; let q:= T (A.B.a.clock.J (m+1)); let z:=x m; have hg : 1 ≤ z:= (a).fits.delayed _|>.le; have hh:0<z:=zero_lt_one.trans_le hg; let w:=hard a m; let t:=gStep β; have hu:0 ≤ w:= (reserve_bounds a m).1.le
 change p^k*(w*z^(-(q:ℝ)))≤ w*t^v; unfold p; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left ?_ hu
 have hB:=blue (A:=A) hβ; have ht: z⁻¹ ≤ t:=by
     have hb': β ≤ 2*z:= hβ.2; have he' : Real.sqrt β≤z:= (Real.sqrt_le_iff.mpr ⟨hh.le,(by change 2 ≤ z at hx; nlinarith)⟩)
     exact inv_anti₀ (Real.sqrt_pos.mpr hB.2.1) he'
 calc
   _ ≤ z * z ^ (-((v+1:ℕ):ℝ)):= mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hg (neg_le_neg (by exact_mod_cast hz))) (Real.rpow_nonneg hh.le _) hh.le
   _ = (z⁻¹)^v := by rw [Real.rpow_neg hh.le,Real.rpow_natCast,pow_succ',inv_pow]; field_simp
   _ ≤ t^v := pow_le_pow_left₀ (inv_pos.mpr hh).le ht _
-- per bound at actual.Exact packets `V'/T.Z` constraints.
lemma always_close (h:G.Simple)(k:ℕ):∀ᶠ m in atTop,∀ j ≤ m+k, Close a m j := by
 let x:= Real.sqrt ∘ Real.sqrt ∘ Hull.year a; have hx: Tendsto x atTop atTop:= Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (Corrected.Grows.beta a h))); filter_upwards [hx.eventually_ge_atTop (k:ℝ)] with m hm j hj using (Nat.cast_le.mpr (by omega : j-m ≤ k)).trans hm
end Hull
end YM.Qlocal.Program
