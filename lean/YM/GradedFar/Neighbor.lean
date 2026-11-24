import YM.GradedFar.Coat
/-!
# QScale antecedents: compact neighboring scale changes

`purchase` hypotheses on actual operands; can exercise separately for field & clock.
Use on `F.homogeneous` application. In follow-up results we show what they buy when the ratio grows.
Not claiming yet to prove these *from compact prices for the correlation or earlier packets*.

We also spell out H coherence on cap inclusions (`Included`). This will be supplied at exactly
this H frame, using (still inputs) from StrongBook, not a grade-polynomial hypothesis. Other
fields assertions of Forecast hypotheses aren't being assumed to replace these prices; steps `Stamp` are
exact to the precision through p (p positive).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace Neighbor
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Fleet MS.Tide FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (F:Final C fo S)(J:ℝ→tower S)
   (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "g" => strength G
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν

def Included (d h:ℕ)(hd:d≤h):Prop:= ∀ᶠ r in trail,∀ u:Sec G d,
    assign J r h (up hd u)= F.sector.derivatives.rise hd (assign J r d u)

-- interval orientation chosen both directions to use compact law at each home.
-- This is the fixed ratio-[1/2,2] version and order p of (G.1), *not* its strengthening to growing ratios.
def Stamp (t:ℝ→ℝ)(h:ℕ)(p:ℕ):Prop:= ∃ b:ℝ,0 ≤ b ∧ ∀ᶠ r in trail,∀ T:ℝ,T∈ Icc (1/2:ℝ) 2 →
    opField ((relative J r (r*T) h).toLinearMap - cropK Kt (-Real.log T) p (t r) h) ≤ b*g r^(p+1)
def DialStamp (t:ℝ→ℝ)(p:ℕ) : Prop := ∃ b:ℝ,0 ≤ b ∧ ∀ᶠ r in trail, ∀ T:ℝ,T∈ Icc (1/2:ℝ) 2 →
    ‖((t (r*T):ℝ):ℂ)-crop p (t r) (ϕ (-Real.log T))‖ ≤ b*g r^(p+1)
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)

include H in
lemma start (η:ℝ)(d:ℕ): coeff 1 (Kt η d)=0 := by
    obtain ⟨X,x,v⟩:= H.details.toServed.toPosted.toQuoted.toContract.toMission.toSchemeV.born
    exact Generator.Q.lifted ν Z.scheme Z.criterion M σ η hG X x v
include H in
lemma first_crop (t:ℝ)(η:ℝ)(h:ℕ): cropK Kt η 1 t h= Level.Dial h η := by
   rw [cropK, Finset.sum_range_succ, Finset.sum_range_one]; ext1 x
   rw [LinearMap.add_apply,LinearMap.smul_apply, coeff_conversion, ((H.dilation ν).check.paid η h).zero,
       LinearMap.smul_apply, coeff_conversion, start Z M ν H, pow_zero, one_smul,LinearMap.zero_apply,map_zero,smul_zero]; simp
lemma weightAt {T:ℝ}(hT:0<T){h:ℕ}(i:Toon G h):
    Level.Dial h (-Real.log T) (theory i)= (T:ℂ)^heft (Dframe.flash i) • theory i := by
   rw [Level.exact₀, Extent.token,neg_neg, Real.exp_log hT]
include H in
lemma evaluated (t:ℝ){T:ℝ}(hT:0<T){h:ℕ}(i: Toon G h): cropK Kt (-Real.log T) 1 t h (theory i)=
   (T:ℂ)^heft (Dframe.flash i) • theory i:= by rw [first_crop Z M ν H, weightAt hT]
include hG in
lemma funded_mono : ∀ᶠ r in trail,∀ s∈ Ioc (0:ℝ) r, 0<g s ∧ g s ≤ g r:= by
   filter_upwards [to_log_zoom.eventually_gt_atTop 0] with r hr s hs
   have h:= Real.log_le_log hs.1 hs.2; have he : LogV r ≤ LogV s:=by simpa [LogV, Real.log_inv] using neg_le_neg h
   have hi:= Gauge.slopeConstant_pos hG
   have hr':0< Real.sqrt (G.slopeConstant*LogV r):= Real.sqrt_pos.mpr (mul_pos hi hr)
   have hv:= Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left he hi.le); exact
     ⟨inv_pos.mpr (hr'.trans_le hv), inv_anti₀ hr' hv⟩

-- one enough for the first local expense. KTotal named for su.
def delta (h:ℕ)(r s:ℝ): Sec G h →ₗ[ℂ] Sec G h := (relative J r s h).toLinearMap-Level.Dial h (-Real.log (s/r))
lemma halves {r s:ℝ}(hr:0<r)(hs:r/2 ≤ s)(ht:s ≤ r):s/r ∈ Icc (1/2:ℝ) 2 ∧ r/s∈ Icc (1/2:ℝ) 2:=by
    have hz:0 < s:= (half_pos hr).trans_le hs; refine ⟨⟨(le_div_iff₀ hr).mpr ?_,(div_le_iff₀ hr).mpr ?_⟩,
      ⟨(le_div_iff₀ hz).mpr ?_,(div_le_iff₀ hz).mpr ?_⟩⟩ <;> linarith
include H in
lemma micro (h:ℕ){t:ℝ→ℝ}(hs:Stamp J Z M ν t h 1): ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail,
    ∀ s:ℝ,r/2 ≤ s → s ≤ r → opField (delta J h r s) ≤ b*g r^2 ∧ opField (delta J h s r) ≤ b*g r^2:=by
  obtain ⟨b,hb,L⟩:= hs; obtain ⟨a,ha,A⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp L
  refine ⟨b,hb,?_⟩; filter_upwards [L,funded_mono (hG:=hG),self_mem_nhdsWithin, (ge_mem_nhds ha).filter_mono nhdsWithin_le_nhds] with r E hE (hr:0<r) hA s hv hs
  obtain ⟨h₁,h₂⟩:= halves hr hv hs; have hp:0 < s:= (half_pos hr).trans_le hv; unfold delta; constructor
  · specialize E _ h₁; rw [mul_div_cancel₀ _ hr.ne',first_crop Z M ν H] at E; exact E
  specialize hE s ⟨hp,hs⟩; specialize A (show s∈Ioc (0:ℝ) a from ⟨hp,hs.trans hA⟩) _ h₂; rw [mul_div_cancel₀ _ hp.ne',first_crop Z M ν H] at A; exact
    A.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE.1.le hE.2 _) hb)
end Neighbor
end YM.Integration.GradedFar
