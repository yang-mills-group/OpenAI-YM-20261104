import YM.LocalTaylorR2.Reel.Strand
import YM.LocalTaylorR2.Capstone.Lens
/-! Comparison basket. Strengthens lender AT PRE-L notation via actual Decal R2. No charts assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical
section permits
open CalendarStep
variable {G:Gauge} (U:RG.Stage)(L:Side)
def upfront (B : ℝ) (p : ℕ) (ε:ℝ) := 2*B^(requested (p+1) ε)
def Access (G:Gauge)(x:ℝ)(v:ℕ):Prop := let f:=betaF G x L
    (δE x ≤ 4* (δE f))∧ (3 ≤ v→∀ p≤v,(3+Strand.spelling p)* f^requested 3 (CalendarStep.loss v) ≤ (Time.credit G U*δE x)/4) ∧
    2*x^(-(3/2):ℝ) ≤ δE x/4
-- theorem expose both stress bills
lemma dto {x:ℝ} (hx:0<x):δE x=x^(-(11/10):ℝ):=by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
lemma concentrates {a b f g:ℝ}(_h:0<f)(hq:0<g)(hb:a<b):∀ᶠ x in atTop, f*x^a ≤ g*x^b:=by
   filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hb)).eventually_ge_atTop (f/g),eventually_gt_atTop (0:ℝ)] with x hx hv
   have hh: f ≤ g * x^(b-a) := by rwa [mul_comm,← div_le_iff₀ hq]
   calc _ ≤ g*x^(b-a)*x^a:=by gcongr
        _ =_:=by rw [mul_assoc, ← Real.rpow_add hv,sub_add_cancel]
lemma openP (v:ℕ): ∀ᶠ x in atTop, Access U L G x v:=by
   let z x:=betaF G x L
   have hm:∀ᶠ x in atTop, δE x ≤ 4*δE (z x):=by
     filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (G.slopeConstant * Real.log (L.val:ℝ))] with x hx hv
     have he:z x ≤ 2*x := by unfold z betaF; linarith
     have hs:0<z x:=hx.trans_le (le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G L)); rw [dto hx,dto hs]
     apply le_trans _ (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs he (by norm_num: (-(11/10):ℝ) ≤ 0)) (by norm_num : (0:ℝ) ≤ 4))
     rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx.le,mul_comm 4,mul_right_comm]; apply le_mul_of_one_le_left (Real.rpow_nonneg hx.le _); conv_rhs => rw [mul_comm, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num), ← div_eq_mul_inv]
     apply (one_le_div (by positivity)).2; exact le_trans (Real.rpow_le_rpow_of_exponent_le (x:=2) (by norm_num) (by norm_num : (11/10:ℝ) ≤ 2)) (by rw [Real.rpow_two]; norm_num)
   have ha (p:Fin (v+1)): 3≤v → ∀ᶠ x in atTop,(3+Strand.spelling p)* (z x)^requested 3 (CalendarStep.loss v) ≤ (Time.credit G U*δE x)/4:=by
     intro he; have hc : CalendarStep.loss v ≤ 1/4:= by unfold CalendarStep.loss; rw [inv_eq_one_div]; gcongr; exact le_trans (b:=3+1) (by norm_num) (add_le_add (by exact_mod_cast he) le_rfl)
     let g:=Time.credit G U; have hg:0<g:= Time.credit_pos ..
     have hb:= Strand.spelling_pos p; have h:=(show (0:ℝ) < 3 by norm_num).trans_le (show 3≤3+Strand.spelling p from le_add_of_nonneg_right hb)
     filter_upwards [(concentrates h (div_pos hg (show (0:ℝ)<4 by norm_num)) (show requested 3 (CalendarStep.loss v)< -(11/10:ℝ) by unfold requested; push_cast; linarith only [hc])),eventually_gt_atTop (0:ℝ)] with x hh hx -- charge ζ directly x
     have ht : x ≤ z x:= le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G L)
     exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx ht (by unfold requested; push_cast; linarith)) h.le).trans (hh.trans_eq (by rw [dto hx]; unfold g; ring))
   have hg:∀ᶠ x in atTop,2*x^(-(3/2):ℝ) ≤ δE x/4:=by
     filter_upwards [concentrates (by norm_num:(0:ℝ)<2) (by norm_num:(0:ℝ)<1/4) (by norm_num : (-(3/2):ℝ)< -(11/10)),eventually_gt_atTop (0:ℝ)] with x hx hv
     rw [dto hv]; apply hx.trans_eq; ring
   by_cases he:3≤v; swap; · filter_upwards[hm,hg] with x h hh; exact ⟨h,fun h=>(he h).elim,hh⟩
   filter_upwards[hm,hg,eventually_all.mpr (fun p=>ha p he)] with x h hk hh; exact ⟨h,fun _ p hz=> hh (⟨p,Nat.lt_succ_of_le hz⟩:Fin _),hk⟩
def wheelD (G:Gauge):Decal G where
    rub _ _ _ L _ _ _ U i x:= Access U L G x i
    good P Q E:= by refine ⟨0,fun _ _ _ _ _ _ _ _ _ _=> openP ..⟩

variable {M:Metals G} {D:Rolls M.p} {A:Alloy M D} {m:ℕ}
local notation "T" => A.B.a
local notation "F" => A.B.a.params m
local notation "x'" => A.B.a.clock.hatBeta m
local notation "z" => A.B.a.clock.hatBeta (m+1)
local notation "u" => A.B.a.clock.allowance m
local notation "u'" => A.B.a.clock.allowance (m+1)
local notation "H" => A.B.a.clock.J (m+1)
variable (R:Roost.Factor A)
lemma trust (hf:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(p:ℕ)(hp:p ≤ H)(he:3≤ p): u ≤ 4*u' ∧
    (3+Strand.spelling p)* z^requested 3 (CalendarStep.loss H) ≤ Time.forecastE T m /4 ∧ ∀ ε:ℝ,ε≤1→ upfront x' p ε ≤ u/4∧upfront z p ε ≤ upfront x' p ε :=by
   have hy: Access F (D.L H) G x' H:=by rw [params_eq A.B.valid]; exact hf _ _ (A.B.valid.pays m) _ (step_paid (T) m)
   unfold Access at hy; rw [← Push.PriceCompiler.beta_eq A.B.valid] at hy
   have hz: (1:ℝ) ≤ x':= (A.B.a.fits.delayed _).le; have hx : x' ≤ z := by rw [Push.PriceCompiler.beta_eq A.B.valid]; exact le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G (D.L H))
   refine ⟨hy.1,hy.2.1 (he.trans hp) p hp,fun ε h=> ?_⟩
   have hi : requested (p+1) ε ≤ -(3/2:ℝ):= by unfold requested; push_cast; linarith only [h, show (3:ℝ) ≤ p from by exact_mod_cast he]
   exact ⟨(mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz hi) zero_le_two).trans hy.2.2,mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hz) hx (hi.trans (by norm_num))) zero_le_two⟩
end permits
end YM.LocalTaylorR2.Reel
