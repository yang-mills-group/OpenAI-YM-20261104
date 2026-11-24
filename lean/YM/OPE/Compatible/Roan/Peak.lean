import YM.OPE.Compatible.Roan.Greet
/-! # 2-leaf layout. bulletin weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m n:ℕ}{t C s u z ℓ v a c e r R β:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T} {q:Sender L}(p:Site L.f)(j:Phase){Y:Studio L}{w: Bid.Dir G L.c}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "μ"=> Y.μφ
local notation "S!"=> Spex L Y q j
local notation "G!"=> FWind G s c u C t
local notation "U!"=> RiseT G k s c u C t z a
local notation "B!"=> Λ_B G k s c u C t z a
local notation "Ω!"=> Βuffs G s c C (roomV G 0 z)
local notation "T!"=> Cσ G s c u C t
abbrev beacon (a b c:ℝ):= max (max a b) c
lemma beacons (a b c:ℝ):a≤ beacon a b c∧ b ≤ beacon a b c ∧ c ≤ beacon a b c:= ⟨(le_max_left ..).trans (le_max_left ..),(le_max_right ..).trans (le_max_left ..),le_max_right ..⟩
noncomputable def Jive (n:ℕ)(U A G t s:price):= beacon (2* Duo (U 2) (hikeP G n 2)) (Duo (A 2) (hikeP G n 2)+Duo (reelP G t n 2) (U 2)) (2*(U 2*reelP G s n 2)) -- k unused
noncomputable abbrev Yule (G:Gauge)(k n:ℕ)(s c u C t z a:ℝ):= Jive n (RiseT G k s c u C t z a) (Λ_B G k s c u C t z a) (FWind G s c u C t) (Cσ G s c u C t) (Βuffs G s c C (roomV G 0 z))
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)(hw:‖w‖≤ t)(hA:ReserveQ L p Y w ℓ)
variable {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L p X ℓ)(hp:Funded L X q a k)(hr:0 ≤ ℓ)
local notation "W!"=>worldA L w
include hA hr
omit hv hx hp h ht hc he hw in lemma lapNear (x:Site L.f)(q:RodZ L n)(ht:Dtn p x≤16*ℓ)(he:Inrange L x q ≤ ℓ): ∀ i, Rebound L Y w ℓ (q i):=by
        intro i; apply hides L p Y w hA hr; let z:=Wct L (q i); apply (Dtn_tag p x z).trans; linarith only [he,ht,hr,Win_go L x q i]
include hX hx hp h ht hc he hv hw
lemma Jits (x:RodZ L n)(z':Site L.f): Pulses (Wish2 L q Y j x-Wish2 L q W! j x) (Dtn p z') (Inrange L z' x) ℓ (Yule G k n s c u C t z a) u:=by
       let Z:=Inrange L z' x; let D:= Dtn p z'; let hM:= grantW hw; obtain ⟨ha,hN,hP⟩:= beacons (2* Duo (U! 2) (hikeP G! n 2)) (Duo (B! 2) (hikeP G! n 2)+ Duo (reelP G! T! n 2) (U! 2)) (2*(U! 2*(reelP G! Ω! n 2))) -- patch
       have hΨ(i:Rubric G X): Rebound L Y w ℓ (Sum.inr (shout G X i)):=hides L p Y w hA hr _ (le_trans (hX (shout G X i) i.1.property) (by linarith only [hr]))
       refine ⟨(norm_sub_le ..).trans ?_,fun hp' hq=> ((Cent2 j h ht hc he hv hx hp hw hΨ _ (lapNear p hA hr z' x hp' hq)).trans (mul_le_mul_of_nonneg_right hN (Real.exp_nonneg _))),fun hK hS=>?_⟩
       · refine (add_le_add (ear2 j h ht hc he hv hx hp _) (ear2 j h ht hc he hM hx hp x)).trans ?_; rw [←two_mul]; exact ha
       have he'(i: Fin n): ℓ+D/8 ≤ Dtn p (Wct L (x i)):=by
             have hm:= Dtn_tag p (Wct L (x i)) z'; rw [DtCom (Wct L (x i)) z'] at hm; -- wrong rw first
             linarith only [Win_go L z' x i,hK,hS,hr,hm]
       let e:= norm_sub_le (Wish2 L q Y j x) (Wish2 L q W! j x); have hz:= nonhome p j h ht hc he hv hx hX hp _ he'; have hg:= nonhome p j h ht hc he (grantW hw) hx hX hp _ he'; exact e.trans ((add_le_add hz hg).trans (by rw [←two_mul, ←mul_assoc];exact mul_le_mul_of_nonneg_right hP (Real.exp_nonneg _)))
end
end YM.OPE.Borealis.Galea
