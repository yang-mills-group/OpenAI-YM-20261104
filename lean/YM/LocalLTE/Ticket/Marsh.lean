import YM.LocalLTE.Ticket.Birth
import YM.LocalLTE.Ticket.Millen
/-! ## Entrance fee burn. Deposited from the same birth.Actual d.Raw.K REAL uncertainty. No assumption on top analytic traces. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open ConnectedActivityE6
open Mallow Daisy Charity Lotus
variable {G:Gauge}
open YM.LocalLTE.Dilation Push.AbsoluteSums
open LocalLTE LocalLTE.Ticket LocalLTE.River Extra.Histories Extra.Histories.Doors
variable (G) (p:ℕ)(a:ℝ)
private lemma withinP (c d R:ℝ)(n N:ℕ) (hr:0≤ R)(hp:0≤c) : ∀ᶠ t :ℝ in atTop,c*(Pressure.temp t)⁻¹^n *(Real.exp d * (Real.exp (R*stain t)-1))≤ Real.sqrt (Doors.stain t)* t^(-(N:ℝ)):=by
   let K:=c*Real.exp d *R*Real.exp R
   filter_upwards [stain_beats (n+1+N),eventually_gt_atTop (1:ℝ), eventually_ge_atTop K] with x hx ht hK
   have hw:=Doors.stain_pos x; have hv:0<x:=zero_lt_one.trans ht
   have hz : Real.exp (R*stain x)-1 ≤ R*stain x*Real.exp R:= (Doors.exp_difference _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_of_le_one_right hr (Doors.stain_le _))) (by positivity))
   have he:c*(Pressure.temp x)⁻¹^n ≤ c*x^n:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (Work.E09.temp_pos (by linarith)).le) (temp_cheap ht.le) n) hp
   calc
     _ ≤ c*x^n * (Real.exp d *(R*stain x*Real.exp R)) :=mul_le_mul he (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.one_le_exp (by positivity)))) (by positivity)
     _ = K*x^n*stain x :=by unfold K; ring
     _ ≤ x^(n+1)*stain x:=by apply mul_le_mul_of_nonneg_right _ hw.le; exact (mul_le_mul_of_nonneg_right hK (by positivity)).trans_eq (by ring)
     _ = (Real.sqrt (stain x)*x^(n+1+N))*Real.sqrt (stain x)*x^(-(N:ℝ)):=by rw [Real.rpow_neg hv.le,Real.rpow_natCast,pow_add x (n+1) N]; field_simp; nth_rw 1 [← Real.sq_sqrt hw.le]
     _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (Real.sqrt_nonneg _) hx) (Real.rpow_nonneg hv.le _)
-- independent of period.D
structure BloomP (G:Gauge)(d:ℕ)(b v t:ℝ):Prop where
    warm: 1 ≤ t
    receipt(C:Levels G)(m p:ℕ)(h:C.clock.hatBeta m=t)(he:(C.params m).supportExponent=b): Extra.Histories.fee ((Labels.frames G).level d) (C.budget m) ((localSection G d).footprint (0:Site (C.S.side m p))) (cameras G d) (C.clock.forcedAllowance m) ≤ Real.sqrt (C.clock.forcedAllowance m)*t^v
lemma bloomP (x:ℝ): ∀ᶠ t in atTop,BloomP G p x a t:=by
   obtain ⟨N,hN⟩:= exists_nat_ge (-a)
   let T:= localSection G p; let F:=((Labels.frames G).level p); let c:= cameras G p; have hc:0≤c:=zero_le_one.trans (cameras_ge ..); let R:ℝ:= T.stencil.card
   filter_upwards [withinP c x R (Extra.Histories.degree F) N (Nat.cast_nonneg _) hc, Work.E01.radiusB_tendsto.eventually_ge_atTop (minSide G p),eventually_gt_atTop (1:ℝ)] with t ht hv hs; refine ⟨hs.le,fun C m n h he=>?_⟩
   let A:= C.budget m; have he': Doors.stain t= C.clock.forcedAllowance m:=by rw [← h]; rfl
   let Y:= T.footprint (0:Site (C.S.side m n)); have hx:Y.card ≤ T.stencil.card:= Finset.card_image_le
   have hp: (coverNumber A.B Y:ℝ) ≤ 1:= by have hx := h.symm ▸ hv; exact_mod_cast Doors.close_stencil G p A.B _ hx 0
   have hA : A.mass Y 1≤Real.exp x:=by unfold BudgetPoint.mass; rw [mul_one]; apply Real.exp_monotone; have hx:0 ≤ x:= he ▸ (A.exponent_pos.le); rw [show A.supportExponent=x from he]; exact mul_le_of_le_one_right hx hp
   rw [show _= Extra.Histories.fee F A Y c (C.clock.forcedAllowance m) from rfl, Extra.Histories.fee, fullCost, show A.threshold=temp t from (by rw [← h]; rfl)] -- unnecessary show
   rw [← he']; apply le_trans _ (le_trans ht ?_)
   · apply mul_le_mul_of_nonneg_left _;  · have he:A.threshold=temp t:= h ▸ rfl; positivity [show 0 < temp t from he ▸ A.threshold_pos] -- test
     apply mul_le_mul hA (sub_le_sub_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (Doors.stain_pos _).le)) _) (sub_nonneg.mpr (Real.one_le_exp _)) (Real.exp_pos _).le; exact mul_nonneg (Nat.cast_nonneg _) (Doors.stain_pos _).le
   exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs.le (neg_le.mp hN)) (Real.sqrt_nonneg _)
end YM.PhysicalNext.Repeat.Legato.Spool
