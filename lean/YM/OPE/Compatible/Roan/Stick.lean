import YM.OPE.Compatible.Roan.Rusk
/-! # κ repr comparisons wages. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m n:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)(q:Sender L)(Y:Studio L)(j:Phase)(w: Bid.Dir G L.c)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "μ"=> Y.μφ
local notation "L!"=> majr L
local notation "W!"=> worldA L w
local notation "S!"=> Spex L Y q j
noncomputable def Wish2 (x:RodZ L i):ℝ:= κ2 μ (Spex L Y q j) (Gale L Y x)
noncomputable def Wish3 (x:RodZ L i)(y:RodZ L m):ℝ:=κ3 μ (Spex L Y q j) (Gale L Y x) (Gale L Y y)
-- abbreviations
lemma shift2 (p r:Y.St→ℝ):κ2 μ p r= κ2 L! (yQ L Y p) (yQ L Y r):=by unfold κ2; simp_rw [← shutt L Y]; rfl
lemma shift3 (p r s:Y.St→ℝ):κ3 μ p r s=κ3 L! (yQ L Y p) (yQ L Y r) (yQ L Y s):=by unfold κ3; simp_rw[←shutt L Y]; rfl
-- Whistle variables
end
section
variable {L:Host K T} {q:Sender L} {Y:Studio L} (j:Phase) {w: Bid.Dir G L.c}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "μ"=> Y.μφ
local notation "L!"=> majr L
local notation "W!"=> worldA L w
local notation "Ω!"=> Spex L Y q j
local notation "Δ!"=> Spex L W! q j
local notation "G!"=> FWind G s c u C t
local notation "U!"=> RiseT G k s c u C t z a
noncomputable abbrev Λ_B (G:Gauge)(k:ℕ)(s c u C t z a:ℝ): price:= Tz (hueCost (FWind G s c u C t) z G) (hueCost (FWind G s c u C t) z G) (hueCost (Cσ G s c u C t) z G) a k
local notation "B!"=> Λ_B G k s c u C t z a
local notation "R!"=> reelP G! (Cσ G s c u C t)
-- near comp
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)
variable {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hp:Funded L X q a k)
include h ht hc he hv hx hp
lemma ear2(x:RodZ L m): ‖Wish2 L q Y j x‖ ≤ Duo (U! 2) (hikeP G! m 2):=by
      exact xBin (Fans h ht hc he hv X hx q hp j 2 two_pos) (Bsafe L Y x h ht hc he hv 2 two_pos)
lemma ear3(x:RodZ L m)(y:RodZ L i): ‖Wish3 L q Y j x y‖ ≤ trioK (U! 4) (hikeP G! m 4) (hikeP G! i 4):=by
      exact xTern (Fans h ht hc he hv X hx q hp j 4 (of_decide_eq_true rfl)) (Bsafe L Y x h ht hc he hv 4 (by decide)) (Bsafe L Y y h ht hc he hv 4 (by decide))
variable (hw:‖w‖ ≤ t)(hH:∀ i:Rubric G X, Rebound L Y w ℓ (Sum.inr (shout G X i)))
include hw hH
lemma Wonk : ‖a_ μ Ω! - a_ ((worldA L w).μφ) Δ!‖ ≤ B! 1 *oer u ℓ:=by
       let p:= yQ L Y Ω!; let s:=yQ L W! Δ!; have hg := Plucked h ht hc he hv hw X hx hH _ hp j; have hb := (y_cost L Y (Fans h ht hc he hv X hx _ hp j)); have hf := y_cost L W! (Fans h ht hc he (grantW hw) X hx _ hp j); rw [show a_ μ Ω!-a_ ((worldA L w).μφ) Δ! = a_ L! (p-s) from by rw [show a_ L! (p-s)=a_ L! p-a_ L! s from integral_sub hb.strong hf.strong]; rw [show a_ L! p=_ from shutt L Y Ω!, show a_ L! s=_ from shutt L W! Δ!]]; exact hg.Integral.trans_eq (mul_comm ..)
lemma Cent2(x:RodZ L m)(H:∀ i, Rebound L Y w ℓ (x i)) :
            ‖Wish2 L q Y j x-Wish2 L q W! j x‖ ≤ (Duo (B! 2) (hikeP G! m 2) + Duo (R! m 2) (U! 2))* oer u ℓ:=by
               let y(p:Studio L):= Spex L p q j; have he'(p:Studio L): Wish2 L q p j x= κ2 L! (yQ L p (y p)) (Bird x p):= shift2 L p _ _; have hb(p:Studio L)(hs:Scale p t):Cane L! (Bird x p) (hikeP G! m):= y_cost L p (Bsafe L p x h ht hc he hs); have hf(p:Studio L)(hs:Scale p t): Cane L! (yQ L p (y p)) U!:= y_cost L p (Fans h ht hc he hs X hx q hp j); have h:= κ2_shift («μ»:=majr L) (hf _ hv) (hf _ (grantW hw)) (hb _ hv) (hb _ (grantW hw)) (Plucked h ht hc he hv hw X hx hH _ hp j) (Bridge h ht hc he hv hw x H); rw[he',he']; apply h.trans_eq; simp only [Pi.smul_apply,smul_eq_mul]; unfold Duo Λ_B; ring
lemma Cent3(x:RodZ L m)(y:RodZ L n)(H:∀ i,Rebound L Y w ℓ (x i))(Z:∀ i,Rebound L Y w ℓ (y i)) :
            ‖Wish3 L q Y j x y-Wish3 L q W! j x y‖ ≤ (trioK (B! 4) (hikeP G! m 4) (hikeP G! n 4)+trioK (R! m 4) (U! 4) (hikeP G! n 4)+trioK (R! n 4) (U! 4) (hikeP G! m 4))*oer u ℓ:=by
                  let F(p:Studio L):= Spex L p q j; have he'(p:Studio L): Wish3 L q p j x y= κ3 L! (yQ L p (F p)) (Bird x p) (Bird y p):= shift3 L p _ _ _; have hb{j:ℕ}(p:Studio L)(hs:Scale p t)(q:RodZ L j):Cane L! (Bird q p) (hikeP G! j):= y_cost L p (Bsafe L p q h ht hc he hs); have hf(p:Studio L)(hs:Scale p t): Cane L! (yQ L p (F p)) U!:= y_cost L p (Fans h ht hc he hs X hx _ hp j); have he:=κ3_shift («μ»:=majr L) (hf _ hv) (hf _ (grantW hw)) (hb _ hv x) (hb _ (grantW hw) x) (hb _ hv y) (hb _ (grantW hw) y) (Plucked h ht hc he hv hw X hx hH _ hp j) (Bridge h ht hc he hv hw x H) (Bridge h ht hc he hv hw y Z); rw [he',he']; apply he.trans_eq; simp only [Pi.smul_apply,smul_eq_mul]; unfold trioK Λ_B; ring
end
end YM.OPE.Borealis.Galea
