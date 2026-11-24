import YM.Qlocal.Squall.Metamer
import YM.Qlocal.Versal.MintLeaf
import YM.RGComparison01.AuxGeo
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Squall
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open AllOrder Floe Step Step.PlanV Iron
open Response Ink Ink.Method Ink.Money
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Pace PriceCompiler Further.PhysicalPeriodLimitF933
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
/-!
# Real mark purchase. Financial allowance after width stages. Poly in the *fine Monitor*, grows through heights. Masks.Realignment law separate. Input shapes probe any frames with funded data.Tag Forecast.Legibility first.

 No crude entire f-volume conversion at all. Keep complete mask profiles & thresholds.
-/
open Metric Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll RGComparison01 RGComparison01.Pledge Merge
namespace Purple
open Quipu Sonnet Tern
open Versal Versal.Freshet
variable (G) (L:Side)(a d t:ℝ)
variable (P:Stage) (x y j k r b:ℕ)
local notation "u"=> Delay.fineMonitor G L a
set_option quotPrecheck false
local notation "n"=> 2*radiusB a
local notation "B"=> n
-- select free exponent `s1` (present 0)
noncomputable def climate (q:ℕ)(t:ℝ):= Vase.humid G P.power P.order j k (2*radiusB a) q t d
lemma water (h:0<d):0≤ climate G a d P j k r t:= Vase.humid_nn (ha:=h) ..
noncomputable abbrev αq (a:ℝ):=4*Delay.fineMonitor G L a
noncomputable def gaugeP := (4*Delay.fineMonitor G L a)^j * climate G a d P j k 1 0
lemma gauge_pos (h:0<d):0≤gaugeP G L a d P j k:= mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (Delay.monitor_pos ..).le) _) (water (h:=h) ..)
include L
lemma expenses : RGComparison01.Geo G L (fun a=> climate G a d P j k r t):= by
 unfold climate Vase.humid Vase.basin; push_cast; let w:=(Geo.fixed (G:=G) (L:=L) 2).times (Geo.basic Lantern.Bolt.size); exact ((((((Geo.fixed _).joins w).power _).times (Geo.fixed _)).times (Geo.fixed _)).times (Geo.fixed _))
lemma territory : RGComparison01.Geo G L (fun a=>gaugeP G L a d P j k):= (((Geo.fixed _).times (Geo.by_delay)).power j).times (expenses ..)
section purse
open AllOrder.Burn
open Extra.Iteration
variable (α:Type)[DecidableEq α] [Fintype α]{R:Marker.Census α} (g:α→ℕ)
local notation "I₀"=> Senses R
local notation "J"=> Fin (r+1)
set_option quotPrecheck false
local notation "T"=> Stanza R G g r
noncomputable abbrev ships (s:Senses R):ℝ:= ∑ i:Fin (r+1),∑ j: Fin (i.val+Lagger.dues g s.val+1),gaugeP G L a d P j k
noncomputable abbrev fortune (R: Marker.Census α):ℝ:= ∑ i:Senses R,ships G L a d P k r α g i
include L
local notation "Φ"=> fortune -- prop
lemma ships_p (hd:0<d)(s:Senses R):0≤ ships G L a d P k r α g s:=Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=> gauge_pos (h:=hd) ..
lemma money (hd: 0<d):0 ≤ fortune G L a d P k r α g R:= sum_nonneg (fun _ _=> ships_p (hd:=hd) ..)
lemma payroll (d:ℝ) : Geo G L (fun a=> fortune G L a d P k r α g R):= Geo.expel univ (fun i a=> ships G L a d P k r α g i) (fun i _=> Geo.expel univ (fun t:Fin (r+1)=> fun a=>∑ j:Fin (t.val+ Lagger.dues g i.val+1), gaugeP G L a d P j k) (fun t _=> Geo.expel univ (fun j:Fin (t.val+Lagger.dues g i.val+1)=> (fun a=> gaugeP G L a d P j k)) (fun _ _=> territory G L d P _ k))) -- Tactic implicit binder j
variable {C d' :ℝ}{p:BudgetPoint}(h:Time.Same P p)(hC:p.B ≤ 2 * Pressure.radiusB a)(hd:0<d)
    (U:Stanza R G g r)(hc:(Stanza.son U k).Allows d C) (hP:0 ≤ C)
local notation "F"=> (Stanza.son U k)
include hd h hC
private lemma passes : Vase.humid G p.power p.order j k p.B 1 0 d ≤ climate G a d P j k 1 0:= by
 unfold Vase.humid climate Vase.humid Vase.basin; rw [h.1,h.2.1]; have ha:= Vase.rune_pos G P.order; have hv : 0≤ Vase.shoot G P.order k j 1:= Vase.weather_ge _ _ _ _ _ _ ha.le; have hy:= Extra.Iteration.momentPrice_pos (Vase.fall P.order P.power j) hd; gcongr -- maybe L unused
include hc hP in
theorem paid (s:Senses R)(Z:(Stanza.son U k).Decision){f:Side}(o:α→Site f) {K:ℕ} (hK:K ≤ p.B) (ht:0<t)(hw:t≤1)(hu:p.threshold/t ≤4*Delay.fineMonitor G L a) : PayR p (Tale.court p.B (o (Sonnet.root s))) (fortune G L a d P k r α g R * C) (Tale.wake s F ((F).short Z K) o t) := by -- o period different! fix
 let x:=o (Sonnet.root s); let I := F; have he :PayR p (Tale.court p.B x) _ _ := Tale.shortBook p (Equiv.refl _) s F Z o (t:=0) (d:=0) (by simp) le_rfl le_rfl hd (v:=0) le_rfl (by rw [zero_add,add_zero]; exact hc) hK ht; rw [zero_mul,neg_zero,Real.exp_zero,mul_one] at he; apply he.enlarge; refine le_trans (b:=ships G L a d P k r α g s*C) ?_ (mul_le_mul_of_nonneg_right (single_le_sum (fun s _=> ships_p G L a d P k r α g hd s) (mem_univ _)) hP); unfold Tale.grand ships; simp_rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _=> Finset.sum_le_sum (fun j _=>?_)
 unfold Tale.gold; let j':=j.val; change _≤ (_^j' * (climate G a d P j.val k 1 0))*_
 apply mul_le_mul_of_nonneg_right _ hP; apply mul_le_mul _ (passes G L a d P _ _ h hC hd) (Vase.humid_nn _ _ _ _ _ _ _ _ hd) (pow_nonneg (mul_nonneg (by norm_num) (Delay.monitor_pos ..).le) _); refine (mul_le_of_le_one_left (pow_nonneg (div_nonneg p.threshold_pos.le ht.le) _) (pow_le_one₀ ht.le hw)).trans (pow_le_pow_left₀ (div_nonneg p.threshold_pos.le ht.le) hu _)
end purse
end Purple
end YM.Qlocal.Squall
