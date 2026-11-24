import YM.RG12.Budget.Report
import YM.PertExtension.Running
import YM.OPE.Columns.SectorCost

/-!
# Adapter: reporting clock/price calculations at k after extraction

Use `B` from the same genuine path+extraction as the continuum table, e.g.
from RG17.single_construction. `g` is never the calendar one. `along_run`
gives exact meaning. These elementary bounds are for paying powers of the
actual expansion parameter at readout; they do **not** prove any formal
reset convergence. `Along` describes the reporting geometry in the consumer
below, not an assertion that any particular `Campaign` pays the further
admission gates in that geometry, nor that for all small r the family uses a
level in that interval. Use any filter on lengths/layouts within such a
window to ask for simultaneous eventual estimates there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Report
open RG Filter Lattice Wilson OPE PertExtension
open scoped Topology BigOperators
variable {G : Gauge}

def lambda (C : Family G) (m : ℕ) : ℝ := 2 + Real.log (C.path.levels.clock.hatBeta m)

def coupling (B : ℕ → ℝ) (m : ℕ) : ℝ := (Real.sqrt (B m))⁻¹

variable {C : Family G}

theorem fitsLambda (C : Family G) (m : ℕ) : 1 ≤ lambda C m := by
  unfold lambda; linarith [Real.log_pos (C.path.levels.fits.delayed m)]

private lemma hat_rate (H : G.Simple) : RateIs atTop C.S.scale C.path.levels.clock.hatBeta 0 :=
  ⟨Eventually.of_forall (fun m => (zero_lt_one.trans (C.path.levels.fits.delayed m))),
    (MergeProof.Ribbons.hut C H).pitch⟩

lemma lambda_rate (hG : G.Simple) : RateIs atTop C.S.scale (lambda C) 0 := by
  have ht:=C.S.divergent
  let u := fun m => 2 + C.path.levels.clock.hatBeta m
  have h : RateLE atTop C.S.scale u 0:= (RateLE.const (2:ℝ) ht).add ((hat_rate hG).pays ht) ht
  refine RateIs.of_sandwich (RateIs.const ht zero_lt_one) h (Eventually.of_forall (fitsLambda C)) (Eventually.of_forall fun i=> ?_) ht
  unfold lambda
  have h' := Real.log_le_sub_one_of_pos (zero_lt_one.trans (C.path.levels.fits.delayed i))
  unfold u; linarith

lemma spacing_rate (C : Family G) : RateIs atTop C.S.scale C.S.a (-1) :=
  ⟨Eventually.of_forall C.S.a_pos,(MergeProof.Ribbons.Note.note_a C.S).pitch⟩

variable {h : C.Makes} {f : Extraction.Order} {B : ℕ → ℝ}

section Ledger
variable (hC : C.Makes) (hG : G.Simple) (hl : Running.isLimit C f B)
include hC hG hl

def betaBand (C : Family G) (B : ℕ → ℝ) := ∀ m, C.path.levels.clock.hatBeta m / 2 ≤ B m ∧
  B m ≤ 2 * C.path.levels.clock.hatBeta m

lemma band : betaBand C B := fun m => Running.band f C hC hG hl m
lemma above (m : ℕ) : 0 < B m :=
  lt_of_lt_of_le (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed m))) ((band hC hG hl m).1)
lemma coupling_pos (m : ℕ) : 0 < coupling B m := inv_pos.mpr (Real.sqrt_pos.mpr (above hC hG hl m))

lemma beta_grows : Tendsto B atTop atTop := by
  let w := C.path.levels.clock.hatBeta
  have ht : Tendsto (fun m=> (1/2:ℝ)*w m) atTop atTop:= (Next.Rank.Station.hat_rate C.path.levels hG).const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono (fun m=> ?_) ht
  have hx := (band hC hG hl m).1; change w m/2 ≤ _ at hx; linarith

lemma coupling_small : Tendsto (coupling B) atTop (𝓝[>] 0) :=
  tendsto_inv_atTop_nhdsGT_zero.comp (Real.tendsto_sqrt_atTop.comp (beta_grows hC hG hl))

lemma observed_run (m : ℕ) : Tendsto (fun i : ℕ × ℕ=> Pert.Asymptotics.regulatorRun C i.1 i.2 m) f.fuse (𝓝 (coupling B m)) :=
  (Real.continuous_sqrt.continuousAt.tendsto.comp (hl m)).inv₀ (Real.sqrt_pos.2 (above hC hG hl m)).ne'

lemma currency (m : ℕ) : C.path.levels.clock.hatBeta m * coupling B m ^ 2 ≤ 2 := by
  rw [coupling,inv_pow,Real.sq_sqrt (above hC hG hl m).le, ← div_eq_mul_inv]
  have hx:= (band hC hG hl m).1
  rw [div_le_iff₀ (above hC hG hl m)]; linarith

-- spatial currency for matrix readout only
lemma coupling_rate : RateIs atTop C.S.scale (coupling B) 0 := by
  let w := C.path.levels.clock.hatBeta
  have ht := C.S.divergent
  have hf : RateIs atTop C.S.scale (fun m=>w m/2) 0:=by simpa only [sub_zero] using ((hat_rate (C:=C) hG).div (RateIs.const ht zero_lt_two))
  have hg : RateIs atTop C.S.scale (fun m=>2*w m) 0:=by simpa only [add_zero] using ((RateIs.const ht zero_lt_two).mul (hat_rate (C:=C) hG))
  have hb: RateIs atTop C.S.scale B 0:= RateIs.of_sandwich hf (hg.pays ht)
    (Eventually.of_forall fun i=> (band hC hG hl i).1) (Eventually.of_forall fun i=> (band hC hG hl i).2) ht
  change RateIs atTop C.S.scale (fun i=> (Real.sqrt (B i))⁻¹) 0
  simpa only [mul_zero,neg_zero, Real.sqrt_eq_rpow] using! (hb.rpow (1/2:ℝ)).inv

-- typical currency error smaller than its leading (at operator tests)
lemma lambda_from_coupling (m : ℕ) : lambda C m ≤ 4 * RG12.Budget.logPrice (coupling B m) := by
  let x := C.path.levels.clock.hatBeta m
  let t := coupling B m
  have hx : 0<x := (zero_lt_one.trans (C.path.levels.fits.delayed _))
  have ht := coupling_pos hC hG hl m
  have h : Real.log (x*t^2) ≤ Real.log 2:= Real.log_le_log (mul_pos hx (pow_pos ht _)) (currency hC hG hl m)
  rw [Real.log_mul hx.ne' (pow_pos ht _).ne', Real.log_pow, Nat.cast_ofNat] at h
  change 2+Real.log x ≤ 4*(1+|Real.log t|)
  linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num),neg_abs_le (Real.log t), abs_nonneg (Real.log t)]

lemma log_fades (p : ℕ) : Tendsto (fun m => coupling B m * lambda C m ^ p) atTop (𝓝 0) := by
  have ht:= (RG12.Budget.log_fades p).comp (coupling_small hC hG hl)
  have h : Tendsto (fun m=> 4^p * (coupling B m * RG12.Budget.logPrice (coupling B m) ^ p)) atTop (𝓝 0):=by simpa only [mul_zero] using! (ht.const_mul (4^p))
  apply squeeze_zero' _ _ h
  · exact Eventually.of_forall fun i => mul_nonneg (coupling_pos hC hG hl i).le (pow_nonneg (zero_le_one.trans (fitsLambda C i)) _)
  filter_upwards with i
  simpa only [mul_pow,mul_left_comm] using! mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (fitsLambda C i)) (lambda_from_coupling hC hG hl i) p) (coupling_pos hC hG hl i).le
end Ledger

section Geometry
variable {I : Type*}

structure Along (C : Family G) (l : Filter I) (m : I → ℕ) (s : I → ℝ) (p : ℝ) : Prop where
  levels : Tendsto m l atTop
  power : 20 < p
  widths : ∀ᶠ i in l, (lambda C (m i) ^ p) ≤ s i / C.S.a (m i) ∧
    s i / C.S.a (m i) ≤ lambda C (m i) ^ (p+1)

variable {l : Filter I} {m : I → ℕ} {s : I → ℝ} {p : ℝ}
variable (hG : G.Simple) (U : Along C l m s p)

include hG U
lemma Along.rate : RateIs l (C.S.scale ∘ m) s (-1) := by
  let a := C.S.a ∘ m
  have hq := (spacing_rate C).comp U.levels
  have ht := (lambda_rate (C:=C) hG).comp U.levels
  have hf : RateIs l (C.S.scale ∘ m) (fun i => lambda C (m i)^p * a i) (-1):= by simpa only [Function.comp_apply, a,mul_zero, zero_add] using ((ht.rpow p).mul hq)
  have hg : RateIs l (C.S.scale ∘ m) (fun i => lambda C (m i)^(p+1) * a i) (-1):= by simpa only [Function.comp_apply, a,mul_zero, zero_add] using ((ht.rpow (p+1)).mul hq)
  have hv:= C.S.divergent.comp U.levels
  exact RateIs.of_sandwich hf (hg.pays hv) (U.widths.mono (fun i ⟨he,_⟩ => (le_div_iff₀ (C.S.a_pos _)).mp he))
    (U.widths.mono fun i ⟨_,hh⟩ => (div_le_iff₀ (C.S.a_pos _)).mp hh) hv

lemma Along.shrinks : Tendsto s l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨(U.rate hG).tends (by norm_num) (C.S.divergent.comp U.levels),(U.rate hG).pos⟩

lemma Along.log_ratio (hC : C.Makes) (hl : Running.isLimit C f B) :
    Tendsto (fun i=> coupling B (m i) ^ 2 * Real.log ((s i)⁻¹)) l (𝓝 G.slopeConstant⁻¹) := by
  have hL : Tendsto (fun i => Real.log ((s i)⁻¹)/C.S.scale (m i)) l (𝓝 1) := by
    simpa only [neg_neg,Function.comp_apply] using (((U.rate hG).inv).rate)
  have hb:= (Running.discrete f C hC hl).comp U.levels
  rw [← Running.slope] at hb
  have hv := hL.div hb (Gauge.slopeConstant_pos hG).ne'
  rw [one_div] at hv
  apply hv.congr'; filter_upwards [(C.S.divergent.comp U.levels).eventually_gt_atTop 0] with i hi
  have hp:=above hC hG hl (m i); change 0 < C.S.scale (m i) at hi
  change Real.log _ / _ / (B (m i) / C.S.scale (m i)) = _
  rw [coupling, inv_pow,Real.sq_sqrt hp.le]; field_simp
end Geometry
end YM.RG17.Report
