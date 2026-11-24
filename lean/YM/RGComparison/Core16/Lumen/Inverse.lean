import YM.RGComparison.Core16.Lumen.Frame

/-! # Paying sparse inverse uniformly

Arity support exp. All p (this in predecessor finite-order physical top-step receipt; not output
Gram!). Use tilted coercivity proof on **native lattice direction at both legs**. Enough without
strips over the width not priced. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Planet
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge Push.AbsoluteSums.Animals Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
open Finset
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}{P:Planet X S ι k T} (H:P.Steady)

abbrev station (P:Planet X S ι k T)(i:Wire G ι):=P.loc i.1
def percent (G:Gauge) (X:Prices):= X.K*Fintype.card G.ColorIndex

omit [Fintype T] [Fintype k] [Fintype ι] in
lemma tip_cost (j:k)(i:Wire G ι) : ‖P.tip j i‖ ≤ 1:=by
   rw [tip,P.mark_price,Prod.norm_def]; refine max_le (by simp) ?_
   rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro t; change ‖portrait _ _ t‖ ≤ 1; unfold portrait; cases he:P.stem j t with
   | none => simp
   | some u => by_cases h:u=i.1 <;> simp [one,h]

include H
lemma quota_paid : Multiplicity P.station (percent G X.sector):= by
   intro i
   let Z:= univ.filter fun j=> P.loc j=i
   have hZ : Z.card ≤ X.sector.K:= (H.tickets 0 ⟨le_refl _, H.prices.thick.2.1.le⟩).core _
   calc _ ≤ (Z ×ˢ (univ:Finset G.ColorIndex)).card:= card_le_card (fun p hp => mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2⟩, mem_univ _⟩)
        _ ≤ _ := by rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ hZ

lemma tip_absent (j:k)(i:Wire G ι)(hi:i.1∉P.soil j):P.tip j i=0:=by
    rw [tip,P.mark_price]; refine Prod.ext rfl ?_; funext t; change portrait _ _ t=0; unfold portrait; cases he:P.stem j t with
    | none=> rfl
    | some u=> have h:u≠i.1:=fun e=>hi (e ▸ H.thread j t u he); simp [one,h]
lemma absent (i j : Wire G ι) (he : 2*X.sector.b < separation (P.station i) (P.station j)) : P.plank i j=0:=by
    refine sum_eq_zero fun a _=>?_ ; by_cases hi:i.1 ∈P.soil a; swap
    · rw [tip_absent H _ _ hi,map_zero]; rfl
    by_cases hj:j.1∈ P.soil a; swap
    · rw [tip_absent H _ _ hj,map_zero]
    have hz : separation (P.loc i.1) (P.loc j.1) ≤ 2*X.sector.b:=(member ..).1 (P.soil_heat ((P.in_heat ..).1 hi) hj)
    exact absurd hz he.not_ge

def ferris [Fintype A] (X:Shelf G A D):= ∑ a, ‖shelfH X a‖
def timber [Fintype A](X:Shelf G A D) := ferris X * weights X.sector X.sector.b
variable [Fintype A]
omit H in
lemma ferris_nn : 0≤ferris X:= sum_nonneg fun i _=> norm_nonneg (shelfH X i)
omit H in
lemma timber_nn : 0≤timber X:= mul_nonneg ferris_nn (Forge.weights_pos ..|>.le)

lemma plank_cost (i j : Wire G ι) : |P.plank i j| ≤ timber X := by
   let I:= P.within i.1; let f a:= shelfH X (P.glyph a) (P.tip a i) (P.tip a j)
   have hv a (ha:a∉I): f a=0:=by unfold f; rw [tip_absent H a i (fun hx=>ha ((P.in_heat ..).1 hx)),map_zero]; rfl
   have hj : (I.card:ℝ) ≤ Forge.weights X.sector X.sector.b:=Nat.cast_le.mpr (price_cover ((H.tickets 0 ⟨le_refl _, H.prices.thick.2.1.le⟩).edge) _ _)
   rw [show P.plank i j=∑ a∈I,f a from (Finset.sum_subset (subset_univ I) (fun i _ hx=>hv _ hx)).symm]; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>ferris X) (fun a _=>?_)).trans ?_)
   · have hy:= show ‖shelfH X (P.glyph a)‖ ≤ ferris X from single_le_sum (fun j _=> norm_nonneg (shelfH X j)) (mem_univ _)
     have he:= (shelfH X (P.glyph a)).le_of_opNorm_le_of_le hy (tip_cost (P:=P) a i)
     rw [mul_one] at he
     exact (((shelfH X (P.glyph a) (P.tip a i)).le_of_opNorm_le_of_le he (tip_cost (P:=P) a j)).trans (mul_one _).le)
   rw [sum_const,nsmul_eq_mul]; unfold timber; rw [mul_comm (ferris X)]; exact mul_le_mul_of_nonneg_right hj ferris_nn

def siegel (X:Shelf G A D):= timber X * Real.exp ((2*X.sector.b:ℕ):ℝ)
omit H in lemma seal_nn : 0≤ siegel X:= mul_nonneg timber_nn (Real.exp_pos _).le
lemma span_paid : Sealed P.station 1 P.plank (siegel X) := by
    intro u v
    by_cases hi: 2*X.sector.b < separation (P.station u) (P.station v)
    · rw [absent H u v hi,abs_zero]; exact mul_nonneg seal_nn (Real.exp_pos _).le
    apply (plank_cost H u v).trans; unfold siegel; unfold Decay
    rw [mul_assoc, ← Real.exp_add]; apply le_mul_of_one_le_right timber_nn; apply Real.one_le_exp
    push Not at hi; simp; exact_mod_cast hi

def depth (X:Shelf G A D):= tiltWidth (percent G X.sector) (chip X.sector) 1 (siegel X)
-- Expose prices as useful functions after postL. NEVER using continuity of inverse in p as premise.
def depthFare (X:Shelf G A D):=((chip X.sector)/2)⁻¹*((percent G X.sector:ℝ)*countCost (depth X))
omit H in lemma depth_zero : 0<depth X:= tiltWidth_pos _ chip_pos zero_lt_one seal_nn
variable [DecidableEq ι] -- potential mismatch elaborator! supp abs uses prior instances.
lemma padded : Sealed P.station (depth X) P.plank⁻¹ ((chip X.sector/2)⁻¹) := inverse_sealed (span_paid H) chip_pos zero_lt_one (forge_piece H) seal_nn (quota_paid H) (isUnit_iff_ne_zero.mpr ((forge_plate H).det_pos.ne'))
lemma earmark (i:Wire G ι): ∑ j,|(P.plank⁻¹) i j| ≤ depthFare X := (padded H).row depth_zero (inv_pos.mpr (half_pos chip_pos)|>.le) (quota_paid H) i
end YM.RGComparison.Core16.Lumen.Planet
