import YM.FVA2.Hearth.Clock
/-!
 # Checking physical tags. Native Haar conditional cost (germ) keeps normalized noise

 Optional check-price by averaging with *actual* S tag weights. Below is **this
 inversion quotient model**, not the path for the cover/Budget estimates (here
 there are e.g. no harmonic zero modes in the gluon propagator). Assembly property uses one shared
 Theta in ALL kernels on the indicated epoch. Exact near-to-start at fixed geometry,
 no claiming exterior likelihood policy must coincide. Need only the germ even for
 sewing in the cap at future steps. Using that proof also for all S predictor tags
 retained on the rooted blocks.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {c f n:Side} {L:Fabric G n}
section
variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)
include H in
lemma true_meets : ∀ᶠ U:LinkFrame G f in 𝓝 1,∀ b:ℝ,∀ V:LinkFrame G c, mixture S U V b=noise S t U V b:= by
 filter_upwards [same_choice S H t] with U h b V;
 have he(v:S.Choices):noise S v U V b=noise S t U V b:= by unfold noise BlockGauge.penalty; rw [show atStep S v U = atStep S t U from funext fun i=> congr_fun (h v) i.val]
 unfold mixture; simp_rw [he]; rw [← Finset.sum_mul, StepData.chosen S H (Orb.liftLinks U),one_mul]
end
-- compare to full normalization (world). At any chosen interior coupling. uses possibly varying physical likelihood at the chosen Costume hierarchy.
 def worlds {n: Side}(L:Fabric G n)(w:L.Cost→ℝ)(x:L.LinksOn): ℝ:= match L with
 | .endcap _ _=>1
 | .layer S H t hf L=> mixture S ((layer S H t hf L).principal x) (L.principal (future S H t hf L x)) (w none) * worlds L (w ∘ some) (future S H t hf L x)
lemma made {n:Side}(L:Fabric G n) : ∀ᶠ x:L.LinksOn in 𝓝 1,∀ w:L.Cost→ℝ, worlds L w x=L.bright w x:= by
 cases L with
 | endcap k h=>
    refine Filter.Eventually.of_forall (fun x w=>?_); unfold Fabric.bright; rw [Fabric.zero_tax]; simp [worlds,Fabric.thermostat]
 | layer S H t hf L=>
    let T:= layer S H t hf L
    have hm:Tendsto T.principal (𝓝 1) (𝓝 1):= T.principal_cont.tendsto _; have hx:Tendsto (future S H t hf L) (𝓝 1) (𝓝 1):= (future_cont S H t hf L).tendsto _
    filter_upwards [hm.eventually (true_meets S H t), hx.eventually (made L)] with x h k w; rw [worlds,Fabric.every]; exact congr_arg₂ (· * ·) (h _ _) (k _)
termination_by structural L
variable (T:Cloth L) (K:Gear L) (N:ℕ) (y:Flats G (Bottom L))
local notation "W"=> Gear.sheets K N
 def betas (t:ℝ)(i:L.Accounts) := ((K.tick N t i)^2)⁻¹
local notation "B(" u ")"=> betas K N u
lemma bills (u:ℝ)(x:L.LinksOn) : L.spend (B(u)) x= L.spend (fun i=> W i u) x / u^2:= by unfold Fabric.spend; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; unfold betas; rw [← K.bill]; ring

-- literal true prefix cost for Gear versus world.W includes the pure `pedal` stripped.
lemma originated (t:ℝ)(ht:t≠0)(x:Warm T→G.El) (a:L.LinksOn) (h:a=committed T y t x):
 fuel T W y t x = Real.exp (-1) * Real.exp (- Fabric.wilson (L.principal a) / t^2) * (L.thermostat (B(t) ∘ some)* L.bright (B(t) ∘ some) a):= by
 have hz: (B(t)) none=(t^2)⁻¹:= by unfold betas; rw [Gear.fires];
 rw [mul_assoc (Real.exp (-1)),show Real.exp (- Fabric.wilson (L.principal a) / t^2)=L.splitFee (B(t)) (L.principal a) from by unfold Fabric.splitFee; rw [hz]; congr 1; ring,← Fabric.income_expr, ←Real.exp_add, bills]; unfold fuel Facade.front; rw [h]
 congr 1; field_simp; ring
end YM.FVA2.Hearth
