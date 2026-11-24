import YM.Contacts.Junction.Dining
/-! # Estimate canonical normalization.Turn. Point jet coherence. 
 Keep unnormalized curvature & projection. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a:ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
section global
variable {p:StagePort G U P X k L σ C M n}
local notation "D" => p.dew
lemma transfer_c {x:p.dew.X} (h:StagePort.Up p v a j) (hP:LocalRatio P) {T:ℝ}
  (hv:∀ z∈Metric.closedBall (0:p.dew.Y) T, let y:=p.flag • x; let s:=windmill (D).B (p.shiftV y z); s∈ Next.SectorChange.mouth P ∧
       (D).grad^p.sizes * (Next.SectorChange.pay P s * traceK p y (stainP p y z))= p.dream y* (Shield.lens₀ (D).matrix⁻¹ z* shadeV p x z)) : let y:=p.flag • x;
       ∫ i in linearStay (D) T y, p.traceK y i ∂(D).B.order G = p.dream y*∫ z in closedBall 0 T,shadeV p x z ∂p.μ:= by
   intro y; have hp :0<(D).grad:= (Fare.gS _ h.truePE.intake.positive).1; obtain ⟨U,hU,hX⟩:= h.truePE.service; have hM := (Lapis.wakes (D).B (D).label (D).T.up (D).T.high (D).ρ σ C _ U h.truePE.stitches.large h.truePE.staples hU 0 (by rw [norm_zero]; exact hU.x_pos)).1; unfold linearStay; rw [Fare.cubits _ P _ _ _ _ _ hp hP (fun z hz=> (hv z (mem_closedBall_zero_iff.mpr hz)).1) ((StagePort.billsV h y).2.meas.stronglyMeasurable),← MeasureTheory.integral_const_mul, StagePort.μ,← MeasureTheory.integral_indicator measurableSet_closedBall, ← MeasureTheory.integral_indicator measurableSet_closedBall, Blaze.Shield.recommends _ (show (D).matrix.PosDef from hM).inv]; -- first rewrite indicator maybe left; edit
   let B:= closedBall (0:(D).Y) T; let F := p.traceK y; let q(z:(D).Y):=(D).grad ^ p.sizes * (Next.SectorChange.pay P (windmill (D).B (p.shiftV y z))* F (p.stainP y z)); change _ = _;
   rw [← MeasureTheory.integral_const_mul]; apply integral_congr_ae; filter_upwards with z; by_cases hx:z∈B; · erw [indicator_of_mem hx,indicator_of_mem hx]; exact (hv z hx).2
   erw [indicator_of_notMem hx,indicator_of_notMem hx]; ring
end global
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
namespace Travel
open Loom.Patch
variable (p:Travel N Q Φ)(hk:2≤k)(hn:k≤n)(hG:G.Simple)(hp:LocalRatio P)(hd:0<d)
local notation "g" => (arcCoast Φ d)
local notation "α" => (fun i z x=> StagePort.crab (Φ i) x z)
local notation "Z" => Frame.Bank (fun i=>(Φ i).dew.X) (fun _=>1)
include p hk hn hG hp hd
lemma glow : ∀ᶠ i in atTop, let v:= Φ i; Measurable v.natal∧ ∀ x∈ Z i, IntegrableOn (v.shadeV x) (closedBall 0 (g i)) v.μ ∧ IntegrableOn (v.warmth x) (closedBall 0 (g i)) v.μ := by
    obtain ⟨d',a,j,_,_,H⟩:=p.ship; filter_upwards [p.warm_cash hk hn hG hp hd,p.flowFee hk hG hp hn,H,p.warm_precise hk hn hG hp hd (show -(1:ℝ)<0 by norm_num)] with i hi hg hx ht v; have h:= hx.2; replace hg:= hg.1; let D:= v.dew; let u:= D.β; let g':= D.grad;
    have hq : Measurable v.natal := (ribbon_caps P D.B D.T D.label D.L h.truePE.staples h.truePE.stitches.large hp).add ((measure_port h.lit).comp (( (clockF (G:=G) D.B).continuous.prodMk ((laneH _).comp D.ℓ.continuous)).measurable)); refine ⟨hq,fun x hh=>?_⟩; let F:=v.bench; have hF: Measurable F:= hg; let f(y:D.Y):=v.crab x y; have hd : Continuous f:=by unfold f StagePort.crab; fun_prop;
    have hx: Measurable (v.warmth x):= by
       have hh: Measurable (skel F 3):= (continuous_iff_continuousAt.mpr (fun i=>(skel_analytic ..).continuousAt)).measurable; exact Real.measurable_exp.comp (((hF.sub hh).comp hd.measurable).const_mul _)
    let B:=closedBall (0:D.Y) (g i); have hv: MeasurableSet B:= measurableSet_closedBall; let s:= {z:D.Y| utterance v (v.flag • x) z}; let K:= v.shadeV x; have hs: MeasurableSet s:= by
        let L':= (fun z:D.Y=> D.B.drape (v.stainP (v.flag • x) z)); have heL : Continuous L':= by unfold L' stainP; refine Continuous.comp («g»:=Forest.drape (G:=G) D.B) (f:=fun z:D.Y=> Fare.draw D.B _ _) D.B.continuous_drape ?_; refine Continuous.comp («g»:= Fare.draw D.B (Cove.ship (v.flag • x))) (Fare.draw_cont D.B _) ?_; unfold shiftV; fun_prop
        exact (flags_measurable_eq v.budget.threshold ∅).preimage heL.measurable
    have he (z:D.Y): (K z= s.indicator (v.warm x) z):= by
        unfold K shadeV; by_cases h:z∈s; · exact (if_pos h|>.trans (Set.indicator_of_mem h _).symm);
        exact (if_neg h|>.trans (Set.indicator_of_notMem h _).symm)
    rw [show v.shadeV x=s.indicator (v.warm x) from funext he]; refine ⟨((MeasureTheory.Integrable.of_bound (hx.mul ((Measurable.const_mul ((hF.sub hq).comp hd.measurable) _) |>.exp)|>.aestronglyMeasurable) (Real.exp 1^2) ?_ )|>.indicator hs),MeasureTheory.Integrable.of_bound hx.aestronglyMeasurable (Real.exp 1) ?_⟩;
    · filter_upwards [ae_restrict_mem hv] with z hz; exact (Real.norm_of_nonneg (ht x hh z hz).1.le).trans_le (ht x hh z hz).2.1
    filter_upwards [ae_restrict_mem hv] with z hz; exact (Real.norm_of_nonneg (hi x hh z hz).1.le).trans_le (hi x hh z hz).2
end Travel
end Provision
end YM.Contacts.Junction
