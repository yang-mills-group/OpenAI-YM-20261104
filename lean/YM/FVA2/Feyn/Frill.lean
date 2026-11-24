import YM.FVA2.Feyn.Product
import YM.FVA2.Feyn.Scent
import YM.FVA2.Laplace.Bare
/-!
 # All-order bulk Gaussian smear, same rooted site-gauge convention

 For every `PreTest` (observables invariant under the allowed transforms and with the
 stated continuity and germ-smoothness), `grams`,`charged` prove equality of the Wilson
 coefficients even in the smeared calculation. No alternate assertion about e.g. averaging mean-zero site
 variables after changing the origin (would need to keep track of the full Jacobian as well). Use Landau separately
 for the true MS identification, Feynman equivalences here purely on the link-side.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2
namespace Laplace.Jacobs
open Function Set Filter Finset MeasureTheory PertExtension Orb Orbit
open Series Radial GaussianScore Screen
open scoped Topology ContDiff BigOperators Classical
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {f:E→F}{L:E≃L[ℝ] F}(q:Jacobs f L)
 [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure] [MeasurableSpace F][BorelSpace F] (ν:Measure F)[ν.IsAddHaarMeasure]
variable {U K O:F→ℝ}{u k y:E→ℝ}
include q
lemma posted (hs:Steep U)(hp: ContDiffAt ℝ ∞ O 0)(hq:ContDiffAt ℝ ∞ K 0)(h:K 0=1) (hU:u=ᶠ[𝓝 0] U ∘ f) (hF:y=ᶠ[𝓝 0] O ∘ f) (hK: ∀ᶠ x:E in 𝓝 0,k x= meter L (fderiv ℝ f x) * K (f x)): pricetag μ k u y=pricetag ν K U O:= by
 unfold pricetag; refine shed2 (amount L μ ν) ?_ ?_ (ready ν hs h) ( Jacobs.pay_pos .. )
 · unfold rows; rw [q.moment_change μ ν hs hU (K':=O*K) (hp.mul hq) (K:=y*k ) ?_, up]
   filter_upwards [hK,hF] with x hx he; simp only [Pi.mul_apply]; rw [hx,show y x=O (f x) from he]; ring
 unfold rows; rw [q.moment_change μ ν hs hU hq hK, Laplace.up]
end Laplace.Jacobs
namespace Feyn.Scent
open Function Set Filter Finset MeasureTheory PertExtension Orb Orbit
open Laplace Series Radial GaussianScore FormalOPE.RG10.MultiGauge Splice
open scoped Topology ContDiff BigOperators Classical
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {G:Gauge} {n:Lattice.Side} (b:Scent G n) (L:Law (Root G n)) (s: Screen G n E) (ev:Even n.val)
local notation "R"=> Root G n
local notation "V"=> Rep G n
local notation "Δ"=> Root G n × E

def budget (v:V) : ℝ := Wilson.energy (Orbit.ignite v)/2 + warmth L (b.d v)
def dressing (v:V) : ℝ:= hair v * b.FP v
local notation "r"=> Scent.groove b s
local notation "Z"=> b.budget L
local notation "χ"=> outer s.price L

lemma descent : Jacobs s.tilt s.hurdle:= ⟨s.smooth,s.resting,rfl ⟩
lemma scent_j : Jacobs (b.groove s) (b.frameG s):= ⟨b.warm s,b.stop s,rfl⟩
lemma ascent : Jacobs s.ancestry s.hurdle.symm := by
 have h : s.ancestry 0=0:= s.ancestry_zero; refine ⟨s.ancestry_germ,h,?_⟩
 have ht:s.hurdle.toContinuousLinearMap ∘L (fderiv ℝ s.ancestry 0)=ContinuousLinearMap.id ℝ V:= by
    obtain hp:= s.emerging.fderiv_eq (𝕜:=ℝ); rw [fderiv_comp (0:V),h,fderiv_id] at hp; · exact hp
    · rw [h]; exact s.smooth.differentiableAt (by simp)
    exact s.ancestry_germ.differentiableAt (by simp)
 refine ContinuousLinearMap.ext (fun x=> s.hurdle.injective ((DFunLike.congr_fun ht x).trans ( s.hurdle.apply_symm_apply x ).symm))
omit [FiniteDimensional ℝ E] in
lemma lands : ∀ᶠ x:Δ in 𝓝 0, Orbit.ignite (s.tilt x)= Lattice.gauge (gang x.1) (Orbit.ignite (s.σ x.2)):= (tup (continuous_fst.tendsto (0:Δ)) ((aimed s.germ.continuousAt s.origin).comp (continuous_snd.tendsto (0:Δ)))).eventually Orbit.physical
omit [FiniteDimensional ℝ E] in
lemma sent : (budget b L) ∘ s.tilt =ᶠ[𝓝 0] χ ∘ r:= by
 filter_upwards [lands s] with x hx; simp only [comp_apply]; unfold budget; rw [hx, Wilson.energy_gauge, add_comm];rfl
lemma dressing_eq : ∀ᶠ p:Δ in 𝓝 0, b.dressing ( s.tilt p ) * s.relative p= meter (b.frameG s) (fderiv ℝ (b.groove s) p)*s.weight p.2:= by
 filter_upwards [s.orbit_density,b.whence s] with p hp hJ; rw [hJ,dressing]; linear_combination ( FP b (s.tilt p) )* hp -- [show hair (s.tilt p)*s.relative p*(FP b (s.tilt p))= _ from congr_arg (· * FP b (s.tilt p)) hp] -- nlinarith
include ev
lemma steep : Steep (Scent.budget b L) := by
 let S:= Grove.rooted G ev; refine ( (ascent S).steepens ((scent_j b S).steepens ( feasible S.price L (S.viable ev) )) ).germ ?_
 filter_upwards [S.emerging,(ascent S).forwards.eventually (b.sent L S)] with p h hp; exact hp.symm.trans (congr_arg (b.budget L) h)
variable {O:Wilson.Config G n→ℝ} (h:PreTest O)
omit ev
include h
omit [FiniteDimensional ℝ E] in
lemma operates : (O ∘ ignite) ∘ s.tilt=ᶠ[𝓝 0] (s.play O) ∘ Prod.snd:= by filter_upwards [lands s] with x hx; simp only [comp_apply]; rw [hx]; exact h.gauge _ (gang_neg _) _
include ev
lemma aspiring : ContDiffAt ℝ ∞ (O ∘ Orbit.ignite) 0:= by
 let Y:= Grove.rooted G ev; let d:= Prod.snd (β:=Cotree n→ G.Color) ∘ Y.ancestry -- syntax fix
 let Q:= O ∘ ignite ∘ Y.σ
 have hp:Q = Y.play O := rfl; have hσ:d 0=0:= by unfold d; rw [comp_apply,Y.ancestry_zero];rfl
 apply ((by rw [hσ,hp]; exact Y.hearing ev h : ContDiffAt ℝ ∞ Q (d 0)).comp (f:=d) (0:V) ( contDiffAt_snd.comp _ (Y.ancestry_germ.of_le le_top) )).congr_of_eventuallyEq
 filter_upwards [Y.emerging,(ascent Y).forwards.eventually (operates Y h)] with p ht heq; exact ((congr_arg (O ∘ ignite) ht).symm.trans heq) -- careful rw p all occurrences!

-- equality of true FP prescription in full link representative coords.
variable (μ:Measure (Rep G n))[μ.IsAddHaarMeasure]
omit h ev
lemma openSpin : ContDiffAt ℝ ω (Scent.dressing b) 0:= hair_analytic.contDiffAt.mul b.current
@[simp] lemma chooses : Scent.dressing b 0=1:= by unfold dressing; simp
variable [MeasurableSpace E][BorelSpace E] (ν:Measure E)[ν.IsAddHaarMeasure]

def check (O:Wilson.Config G n→ℝ) : PowerSeries ℝ:= Laplace.pricetag μ (b.dressing) (b.budget L) (O ∘ Orbit.ignite)
include h ev
lemma leans : check b L μ O=s.charge ν O:= by
 let φ₀:=Measure.addHaar (G:=R); let ζ := φ₀.prod ν
 let Z':= s.play O ∘ (@Prod.snd R E); let K:= s.weight ∘ (@Prod.snd R E)
 have he: (K 0)=1:=s.head
 let f:= Z' ∘ b.groove s; let H_f:= Laplace.pricetag ζ (fun v=> meter s.hurdle (fderiv ℝ s.tilt v)* b.dressing (s.tilt v)) (budget b L ∘ s.tilt) f
 have hY:H_f=Laplace.pricetag ζ K (χ) Z':= by
    refine (scent_j b s).posted ζ ζ ( feasible s.price L (s.viable ev) ) ((s.hearing ev h).comp (f:=Prod.snd) 0 contDiffAt_snd) ( (s.analytic.of_le le_top).comp (f:=Prod.snd) 0 contDiffAt_snd) he (sent b L s) (EventuallyEq.refl _ _) ?_; filter_upwards [dressing_eq b s] with x hx; exact (mul_comm ..).trans hx
 have ht:H_f=Scent.check b L μ O:=(descent s).posted ζ μ (steep b L ev) (aspiring ev h) ((openSpin b).of_le le_top) (chooses b) (EventuallyEq.refl _ _) ( ( operates s h ).symm ) (Eventually.of_forall (fun _=>rfl))
 rw [←ht,hY]; exact settled _ _ _ L (s.viable ev) (s.analytic.of_le le_top) _ ν s.head (s.hearing ev h)

theorem grams : b.check L μ O= PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= (b.leans L (Grove.rooted G ev) ev h μ (Measure.addHaar (G:=Cotree n→G.Color))).trans (( Grove.rooted G ev ).genuine ev _ h)

lemma charged (Λ:Law (Rep G n))(hk:Λ.kern=Radial.kernel (b.budget L)) : Splice.enjoy Λ μ (Stack.rise (O ∘ Orbit.ignite)) (sink b.dressing (b.budget L))= PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= ( (receipt μ Λ hk (chooses b) ((openSpin b).of_le le_top) (aspiring ev h)).symm.trans (b.grams L ev h μ) )

end Feyn.Scent
end YM.FVA2
