import YM.OPE.Compatible.Calendars.Again
import YM.OPE.Compatible.Assemblage.Whole
/-!
# Ruler for logarithmic operations

Spending $$exp(C \, m)$$ across these cells would not meet the bill! Track
budget decrements once per actual regrouping. Point-facing sufficient
conditions; realtime clearance measured at that ruler independent of
potentially much finer grandchildren.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG MergeProof Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology Classical
variable {G:Gauge} (C:Family G)
set_option quotPrecheck false
local notation "Y"=>C.path.levels
abbrev level (C:Family G):Schedule:= C.path.levels.S
abbrev bins (C:Family G)(i:ℕ): BudgetPoint:= C.path.levels.budget i
abbrev extent (C:Family G)(i:ℕ):ℝ:= ((C.path.levels.S.block i).val:ℝ)
lemma β_one (i:ℕ):1< β C i:= (Y).fits.delayed i
lemma β_pos (i:ℕ) : 0< β C i:= zero_lt_one.trans (β_one ..)
lemma extent_two (i:ℕ): 2 ≤ extent C i:=by exact_mod_cast (show 2 ≤ Nat.succ 2 from by decide).trans ((level C).block_large i)
variable {C} (A:Allot C)
include A
lemma block_cheap (i:ℕ) : extent C i ≤ β C i:=by
   have hx:= A.buy.halos i; let v:=haloUnits ((level C).block i) (bins C i).B (bins C (i+1)).B
   have he : (v:ℝ) ≤ Real.sqrt (β C i):= (le_mul_of_one_le_left (Nat.cast_nonneg _) (show 1≤ (bins C (i+1)).supportExponent+1 from by rw [A.fixed (i+1)]; norm_num)).trans hx
   have hv : extent C i ≤ v:=by
     let c:= level C; let m:= bins C i; let L:ℕ:=(c.block i).val; let t:ℕ:=1+L*(m.B+(bins C (i+1)).B+1)^2
     have ht: 1 ≤ t:=by unfold t;omega
     have hp: L ≤ t:= le_trans (Nat.le_mul_of_pos_right L (show 0 < (m.B+(bins C (i+1)).B+1)^2 from by positivity)) (Nat.le_add_left _ 1)
     change (L:ℝ) ≤ v; exact_mod_cast hp.trans ((pow_one t).symm.trans_le (pow_le_pow_right₀ ht (by norm_num : 1 ≤ (4:ℕ)))) -- 
   apply hv.trans (he.trans _); apply (Real.sqrt_le_left (β_pos ..|>.le)).2; exact le_trans (le_of_eq (pow_one _).symm) (pow_le_pow_right₀ (β_one ..|>.le) (by norm_num))
omit A
variable (hG:G.Simple)
include hG
lemma β_increases : StrictMono (β C):=by
   intro a b he; exact add_lt_add_right (a:= (Y).clock.bar) (mul_lt_mul_of_pos_left (scale_mono C.S he) (G.slopeConstant_pos hG)) -- name add.h
lemma β_ascent : Tendsto (β C) atTop atTop:=by
   unfold β Calendar.hatBeta; exact Filter.Tendsto.add_atTop (f:=fun _=>C.path.levels.clock.bar) tendsto_const_nhds (C.S.divergent.const_mul_atTop (G.slopeConstant_pos hG)) --
lemma fly_le (d i j:ℕ)(he:i ≤ j) : fly (Y) d j ≤ fly (Y) d i:= inv_anti₀ (pow_pos (β_pos C _) _) (pow_le_pow_left₀ (β_pos C _).le ((β_increases hG).monotone he) _)
omit hG
lemma renal_eq (C:Family G) (i:ℕ):renal C.path.levels i=(β C (i+1)^2)⁻¹:= Real.rpow_neg (β_pos C _|>.le) (2:ℝ)|>.trans (congr_arg _ (Real.rpow_two _))
lemma near_eq (C:Family G) (i:ℕ): near C.path.levels i=(β C (i+1))⁻¹:= rfl
lemma fly_eq (C:Family G) (d i:ℕ): fly C.path.levels d i=(β C i^(MergeProof.winter G d))⁻¹:=rfl
include A
lemma columns_save (d i:ℕ)(hi:C.ref d ≤ i): ((Y).params i).columns ≤ β C i^(MergeProof.winter G d) :=by
    -- requires A included
    have hv:=A.buy.system.costs.heights d i i 0 hi le_rfl
    obtain ⟨h,-⟩:= hv.choose_spec; have hc:= h.coin i le_rfl; rw [fly_eq, mul_comm,← div_eq_mul_inv] at hc; exact (div_le_one (pow_pos (β_pos C _) _)).1 hc
end YM.OPE.Allot
