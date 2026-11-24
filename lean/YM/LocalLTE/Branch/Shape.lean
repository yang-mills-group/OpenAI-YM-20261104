import YM.LocalLTE.Branch.Book
/-! Slack pricing POST. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Urns
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- compact socket avoids Pie SAM goals; not obligation records encoding analytic estimates.
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open Magnet YM.LocalLTE.Inset ClockB
variable {G : Gauge} {X: Metals G} {D : Rolls X.p} {s : Sheet G}
section bill
-- no clock asset P needed? P.g used billing. Time context
variable (L: Side) (β : ℝ) {p:ℕ} (c g v v' : ℝ) (C : RG.Stage)
local notation "y" x=> betaF G x L
local notation "f" x=> Delay.fineMonitor G L x
local notation "P" x=> Vac.Numbers.P x
abbrev divisor (x:ℝ) := Real.sqrt (Real.exp (-((Vac.Numbers.P x)^(1/5:ℝ))))
lemma nonzero (x:ℝ):0< divisor x:= Real.sqrt_pos.mpr (Real.exp_pos _)
lemma fogReady (h:0<c) : Rate G L v (fun x=> Real.exp (-c*Delay.fineMonitor G L x^2) / divisor x) := by
  have hx : Rate G L v (fun x=> Real.exp (-(c/2)*(f x)^2)) := by
    simpa only [Real.rpow_two] using Rate.monitor_cutoff (G:=G) (L:=L) (a:=v) (half_pos h) (show 0<(2:ℝ) by norm_num)
  apply hx.compare; filter_upwards [eventually_ge_atTop (Real.exp 1), Delay.wins G L h (u:=1) zero_lt_one (hD:=show 0≤(1:ℝ) from zero_le_one) (show 1/5< (2:ℝ) by norm_num) 0] with t ht hh
  rw [abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (nonzero _|>.le)),abs_of_nonneg (Real.exp_nonneg _),div_le_iff₀ (nonzero t)]; unfold divisor
  rw [Real.sqrt_eq_rpow,← Real.exp_mul, ← Real.exp_add,Real.exp_le_exp]
  have he : (P t) ≤ (f t) := by have hP : 2*(P t) ≤ 2*(f t) := Pane.brace t ht; linarith only [hP] -- loopBill
  rw [pow_zero,mul_one,one_mul] at hh
  change (Delay.fineMonitor ..)^(1/5:ℝ)≤ (c*1* _)/16 at hh
  linarith only [Real.rpow_le_rpow (show 0 ≤ Vac.Numbers.P t from Real.exp_nonneg _) he (show 0 ≤ (1/5:ℝ) by norm_num),hh, Real.rpow_nonneg (x:= P t) (show 0≤ _ from Real.exp_nonneg _) (1/5:ℝ)]
lemma actualG (ε:ℝ) (A:ℝ→ℝ)(r:ℝ) (h:Rate G L r A)(he:r< -ε/2) : ∀ᶠ t in atTop,∀ β, betaF G t L/2≤β→ β ≤ 2* betaF G t L → A t ≤ gStep β^ε:= by
  let g:= -ε/2; let b := min ((1/2:ℝ)^g) ((2:ℝ)^g); have hb:0<b:= lt_min (by positivity) (by positivity)
  filter_upwards [Sienna.contraction G L (a:=1) hb h he,Delay.shift_pos G L] with t hp hy β ht hf
  have hyβ : 0<β:= (half_pos hy).trans_le ht
  have hh: gStep β^ε=β^g:=by
    unfold Coat.gStep; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hyβ.le,← Real.rpow_mul hyβ.le]; unfold g; ring_nf
  rw [one_mul] at hp; rw [hh]; apply hp.le.trans
  by_cases hg:0≤g
  · calc _ ≤ (1/2:ℝ)^g * (y t)^g := mul_le_mul_of_nonneg_right (min_le_left ..) (Real.rpow_nonneg hy.le g)
         _ ≤ β^g := by rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) hy.le]; exact Real.rpow_le_rpow (by positivity) ((show (1/2:ℝ) * betaF G t L=betaF G t L /2 by ring).trans_le ht) hg
  exact le_trans (mul_le_mul_of_nonneg_right (min_le_right ((1/2:ℝ)^g) _) (Real.rpow_nonneg hy.le g)) ((Real.mul_rpow (show (0:ℝ) ≤2 by norm_num) hy.le).symm.trans_le (Real.rpow_le_rpow_of_nonpos hyβ hf (le_of_not_ge hg))) -- args

variable (D) (Q : PostCost D) {Θ: Protection D}
-- Adds priorities. wind AFTER Post gap demand. actual for arbitrary beta in BOTH-band.
def Balance (W: Delays Θ)(p:ℕ) (e η:ℝ) : Prop:= ∀ j i,StepStages j i→ ∀ x≥W.betaEntry j, ∀ β, betaF G x (D.L j)/2 ≤ β→ β ≤ 2*betaF G x (D.L j) →
    let L:= D.L j; let z:= betaF G x L; let P':= Delay.fineMonitor G L x
    let A:=Time.base G (X.p.profile i); let b:=gStep β^(p+1-η:ℝ)
    (A+1)*(z^e) ≤ b ∧ Real.exp (-(Q.g j)*P'^2) / divisor x ≤ b
lemma balances (p':ℕ)(a b:ℝ)(he:a< -(p'+1-b:ℝ)/2)(V:Delays Θ): ∃ W:Delays Θ,DelayLe V W ∧ ∀ U:Delays Θ,DelayLe W U→ Balance D Q U p' a b:=by
  have hm j i: ∀ᶠ x:ℝ in atTop,∀ β,betaF G x (D.L j)/2≤β→ β ≤2*betaF G x (D.L j) → let S:=D.L j; let z:=betaF G x S; let b':=gStep β^(p'+1-b:ℝ); (Time.base G (X.p.profile i)+1)*(z^a) ≤ b' ∧ Real.exp (-(Q.g j)*(Delay.fineMonitor G S x)^2) / divisor x ≤ b':= by
    let L:= D.L j; let P':= X.p.profile i; let e:= (p'+1-b:ℝ)
    filter_upwards [actualG L _ _ _ ((Rate.power (G:=G) (a:=a)).mul_left (Time.base G P'+1)) he, actualG L e _ _ (fogReady L (Q.g j) a (Q.posG j)) he] with x he hf
    exact (show ∀ β, betaF G x L/2≤β→ β ≤ 2*betaF G x L → (Time.base G P'+1)*((betaF G x L)^a) ≤ gStep β^e ∧ Real.exp (-(Q.g j)* (Delay.fineMonitor G L x)^2) / divisor x ≤ gStep β^e from fun i h hh=> ⟨he _ h hh,hf _ h hh⟩)
  obtain ⟨x,-,hx,hV⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ fun i (_:StepStages j i)=> hm j i)
  exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ hw j i he t ht=> hV _ t ((hw.beta _).trans ht) i he⟩
end bill
end YM.PhysicalNext.Repeat.Urns
