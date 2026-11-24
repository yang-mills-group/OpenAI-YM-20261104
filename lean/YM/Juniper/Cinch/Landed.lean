import YM.Juniper.Cinch.Economy
import YM.Juniper.Provider.Nursery
/-!
 # Extra pledge & strong conversion is uniform in (N,n) and true cut rank.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open Filter Function Lattice RG Pressure Pressure.Testing Tree Wilson
open Push Push.AbsoluteSums Precision Next.Fluctuations SectorMeasure
open ConnectedActivityE6 Coat Rain
open Further.PhysicalPeriodLimitF933 Macrame Uniform
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Input Org Supply Opera Pane Roof Push.PriceCompiler ThroughLaunch Blaze Roost Push.Uniform
open Progress.DirectedRecipe Time Legato
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G: Gauge}{X:Metals G}{D:Rolls X.p}{P: Protection D}
structure Courtesy (W:Delays P) : Prop where
    tickets (j i:ℕ): StepStages j i→∀ x,W.betaEntry j ≤ x→scrutiny G (X.p.profile i) j x
lemma purchasable (W:Delays P) : ∃ V: Delays P, DelayLe W V∧Courtesy V:= by
   obtain ⟨f, -,hf,h⟩:= collect_upper W.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i h=> scrutiny_pays G (X.p.profile i) j)); exact ⟨{W with betaEntry:=f},⟨hf,le_rfl,le_rfl,le_rfl⟩,⟨fun j i hj x hx=> h j x hx i hj⟩⟩
def invoice (G : Gauge) : Legato.Booster G where
   asks _ _ _ W:= Courtesy W
   mono h hv:= ⟨fun j i hi x hx=> h.tickets j i hi x ((hv.beta _).trans hx)⟩
   buy _ _ _ W:= purchasable W
section period
open Bid
variable (C:Family G) (hG:G.Simple)
local notation "B"=> C.path.levels
local notation "t"=> C.path.levels.clock.hatBeta
local notation "S"=> C.S
include hG
lemma kettle : ∀ᶠ i:ℕ in atTop,∀ j:ℕ, wraps (t i) ((S).side i j):= by
  filter_upwards [Pert.Kinetic.stay C hG 4 1000000] with i hi j; have ht:= hi j; let r:= t i; let n:= C.side i j; let u:=(n.val:ℝ)
  have hN: 0<u:= by unfold u; positivity
  rw [abs_of_pos (by norm_num : 0<(1000000:ℝ))] at ht; change (2*r)^4 *1000000*((2*Real.pi)/u) ≤1 at ht
  rw [← mul_div_assoc, div_le_one hN] at ht; change (1000*r^2)^2 ≤ u; apply le_trans _ ht; nlinarith only [mul_le_mul_of_nonneg_right Real.two_le_pi (show 0≤r^4 by positivity), show 0≤r^4 by positivity]
end period

variable {hG:G.Simple}{N:Nursery G hG}
noncomputable def pricing (E:Extras G): Extras G:= { E with booster:= E.booster.and (invoice G) }
variable (E : Extras G)(h:Stock (Cinch.pricing E) N)
include E h
lemma behind : Stock E N := { h with boosted:= h.boosted.1 }
lemma vigorously : Courtesy N.A.delay:= h.boosted.2
variable {A: Alloy X D}{r:ℕ}
omit E h
local notation "W"=> A.B.a.budget r
local notation "B"=> A.B.a
lemma issued (h: Courtesy A.delay) : scrutiny G (A.B.a.params r) (A.B.a.clock.J (r+1)) (A.B.a.clock.hatBeta r):= by rw [params_eq A.B.valid]; exact h.tickets _ _ (step_paid A.B.a r) _ (A.B.valid.pays r)
end YM.Juniper.Cinch
