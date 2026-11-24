import YM.OPE.Compatible.Roan.Wick
/-! # Collective polynomial vertices. -/
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
open Lav
section
variable {L:Host K T} {q:Sender L} (p:Site L.f) (j:Phase) {Y:Studio L}{w:Bid.Dir G L.c}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "W!"=> worldA L w
local notation "η!"=> Gov s u
local notation "ζ!"=> burst (Gov s u) ℓ
noncomputable abbrev Push2 (L:Host K T)(q:Sender L)(Y:Studio L)(j:Phase)(f:L.DirA→ℝ):=κ2 Y.μφ (Spex L Y q j) (alongB L Y f)
noncomputable abbrev Push3 (L:Host K T)(q:Sender L)(Y:Studio L)(j:Phase)(f g:L.DirA→ℝ):= κ3 Y.μφ (Spex L Y q j) (alongB L Y f) (alongB L Y g)
noncomputable abbrev price2(G:Gauge)(k m:ℕ)(s c u C t z a r:ℝ):= (r*‖Yule G k m s c u C t z a‖)*tokenCost G m (Gov s u)
noncomputable abbrev price3 (G:Gauge)(k m n:ℕ)(s c u C t z a r R:ℝ):= ((r*R)*‖Yeast G k m n s c u C t z a‖)*tokenCost G n (Gov s u)* tokenCost G m (Gov s u)
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)(hw:‖w‖≤ t)(hA:ReserveQ L p Y w ℓ)
variable {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L p X ℓ)(hp:Funded L X q a k)(hr:0 ≤ ℓ)
variable {f g:L.DirA→ℝ}
include h ht hc he hv hw hA hx hX hp hr
lemma StemV (hP:Tires L f m r s): ‖Push2 L q Y j f-Push2 L q W! j f‖ ≤ price2 G k m s c u C t z a r * ζ!:=by
        obtain ⟨a',hp'⟩:=hP; let I(B:Studio L):=Wish2 (i:=m) L q B j; let V(z: Site L.f)(x:RodZ L m):= a' z x * (I Y x-I W! x); have ht':0≤ r:=hp'.pos
        have he'(B:Studio L): Push2 L q B j f=∑ z,∑ x:RodZ L m,a' z x*I B x:= coinX L B h he ht hc hp' ((Quala L B h he ht hc X hp).Γ j); have hi:= Yule G k m s c u C t z a; let E:= r*‖Yule G k m s c u C t z a‖; have hT:=Gov_price ht h.vein.warmth; have hV(z')(x: RodZ L m): ‖V z' x‖≤ E * ζ! * wigP p η! z' x:=by
              let U:=Yule G k m s c u C t z a; let D:=Dtn p z'; let L':= Inrange L z' x; have hh:‖V z' x‖ ≤ r*U *Real.exp (-η!*(ℓ+D+L')):= Issue hr (DtHi p z') (by linarith only[DtHi p z']) (Win_hi ..) ht h.vein.warmth ht' (hp'.dock z' x) (Jits p j h ht hc he hv hw hA hx hX hp hr x z'); apply hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.le_norm_self _) ht') (Real.exp_nonneg _)).trans_eq ?_); unfold wigP burst; rw [mul_add,mul_add,Real.exp_add,Real.exp_add]; change E*_=_; unfold D L'; ring
        rw [show Push2 L q Y j f-Push2 L q W! j f=∑ p,∑ i, V p i from (by unfold V; simp_rw[mul_sub,sum_sub_distrib,he'])]; exact (Temple p V hV hT.1 (mul_nonneg (mul_nonneg hp'.pos (norm_nonneg _)) (Real.exp_nonneg _))).trans_eq (by unfold price2 E; ring)
lemma StemW (hP:Tires L f m r s)(hS:Tires L g n R s): ‖Push3 L q Y j g f-Push3 L q W! j g f‖ ≤ price3 G k m n s c u C t z a r R * ζ!:=by
        obtain ⟨a',hp'⟩:=hP; obtain ⟨b,hq'⟩:=hS; let I(B:Studio L):=Wish3 (i:=m) (m:=n) L q B j; let V(z':Site L.f)(x:RodZ L m)(r:Site L.f)(y:RodZ L n):=a' z' x*b r y*(I Y x y-I W! x y); have hh(B:Studio L): Push3 L q B j g f=∑ z,∑ x,∑ Z,∑ y,a' z x*b Z y*I B x y:=EarthX L B h he ht hc hp' hq' ((Quala L B h he ht hc X hp).Γ j);
        let U:= Yeast G k m n s c u C t z a; let E:=r*R*‖U‖; have hK:0≤r*R:=mul_nonneg hp'.pos hq'.pos; have hV(z' x z'' y): ‖V z' x z'' y‖ ≤ E*ζ! *wigP p η! z' x*wigP p η! z'' y:=by
             let f:= a' z' x*b z'' y; let D:= Inrange L z' x; let B:= Inrange L z'' y; have ht':‖f‖≤ (r*R)*Real.exp (-(s*(D+B))):=by unfold f; rw [norm_mul]; apply (mul_le_mul (hp'.dock z' x) (hq'.dock z'' y) (norm_nonneg _) (mul_nonneg hp'.pos (Real.exp_nonneg _))).trans_eq; rw [mul_mul_mul_comm, mul_add,neg_add,Real.exp_add]
             let v':=Dtn p z'; let q':=Dtn p z''; let m':=max v' q'; have he:‖V z' x z'' y‖ ≤ (r*R*U)*Real.exp (-η!*(ℓ+(v'+q')+(D+B))):= Issue hr ((DtHi ..).trans (le_max_left ..)) (by linarith only[ le_max_left v' q',le_max_right v' q']) (add_nonneg (Win_hi ..) (Win_hi ..)) ht h.vein.warmth hK ht' (Fares p j h ht hc he hv hw hA hx hX hp hr x y z' z''); apply he.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.le_norm_self _) hK) (Real.exp_nonneg _)).trans_eq ?_); unfold wigP burst; simp_rw [mul_add,Real.exp_add]; change E*_=_; unfold D B v' q'; ring
        rw [show Push3 L q Y j g f-Push3 L q W! j g f= ∑ z,∑ x,∑ r,∑ y,V z x r y from (by unfold V; simp_rw [mul_sub,sum_sub_distrib,hh])]; exact (Prime p V hV (Gov_price ht h.vein.warmth).1 (mul_nonneg (mul_nonneg hK (norm_nonneg _)) (Real.exp_nonneg _))).trans_eq (by unfold price3 E U; ring)
end
end YM.OPE.Borealis.Galea
