import YM.OPE.Compatible.Munch.Aged
/-! # walk price one clustering with nearby escape root only powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f){q:Sender L}{Y:Studio L}
variable (j':Phase)(h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t) {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L x X M)(hp:Funded L X q a k)
-- use modified constants Beast leap
noncomputable abbrev Dig2 (G:Gauge)(k n:ℕ)(s c u C t z a:ℝ) := let U:=RiseT G k s c u C t z a; let Z:=FWind G s c u C t; max (Duo (U 2) (hikeP Z n 2)) (U 2*(reelP Z (Βuffs G s c C (roomV G 0 z)) n 2))
noncomputable abbrev Dig3 (G:Gauge)(k n m:ℕ)(s c u C t z a:ℝ):= let U:=RiseT G k s c u C t z a; let Z:=FWind G s c u C t; let A:=fun i=> Βuffs G s c C (roomV G i z); max (trioK (U 4) (hikeP Z n 4) (hikeP Z m 4)) (max (Alc n m U Z A) (Alc m n U Z A))
include h ht hc he hv hx hX hp
local notation "μ'"=> Gov s u
lemma R2 {f b:ℝ}(p:RodZ L n)(Z:Site L.f)(hF:f= Wish2 L q Y j' p)(ha:0 ≤ A)(hh:‖b‖≤A*Real.exp (-(s*Inrange L Z p))) : ‖b*f‖ ≤ A*‖Dig2 G k n s c u C t z a‖*ticPay x Z p M (Gov s u):=by
         let d:= Dtn x Z; let l:= Inrange L Z p; let T:=Dig2 G k n s c u C t z a; have hs: 0 ≤A*‖T‖:= mul_nonneg ha (norm_nonneg _); subst f; let g:= Wish2 L q Y j' p; have he':‖g‖≤ ‖T‖:= ((ear2 j' h ht hc he hv hx hp p).trans (le_max_left ..)).trans (Real.le_norm_self _); by_cases hR:d ≤16*M
         · exact (swayPay (Win_hi ..) ht h.vein.warmth ha hh he').trans (mul_le_mul_of_nonneg_left (on_J x Z p hR) hs)
         have hu : ‖b*g‖≤ A*‖T‖*Real.exp (-μ'*(d+l)):= by
               apply Norm_K (Win_hi ..) ht h.vein.warmth ha hh (by linarith only [DtHi x Z]) (show 0<d by have hz:0 ≤ (M:ℝ):= Nat.cast_nonneg _; linarith) he'; intro hZ; have hn(i:Fin n): (M:ℝ)+d/8 ≤ Dtn x (Wct L (p i)):= by
                     have hk:= Dtn_tag x (Wct L (p i)) Z; rw [DtCom (Wct L (p i)) Z] at hk; linarith only [not_le.mp hR, Win_go L Z p i,hZ,hk]
               exact (nonhome x j' h ht hc he hv hx hX hp p hn).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (Real.le_norm_self _)) (Real.exp_nonneg _))
         rw [mul_add,Real.exp_add] at hu; exact hu.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (unt_J x Z p)) hs)
lemma R3 {f b:ℝ}(p:RodZ L n)(z':Site L.f)(y:RodZ L m)(Z:Site L.f)(hF:f= Wish3 L q Y j' p y)(ha:0 ≤ A)(hh:‖b‖≤A*Real.exp (-(s*(Inrange L z' p+Inrange L Z y)))) : ‖b*f‖ ≤ A*‖Dig3 G k n m s c u C t z a‖*(ticPay x z' p M (Gov s u)*ticPay x Z y M (Gov s u)):=by
         subst f; let d:= Dtn x z'; let d':= Dtn x Z; let D:= max d d'; let B:= Inrange L z' p; let B':= Inrange L Z y; let F:= B+B'; let q':= Wish3 L q Y j' p y; let T:= Dig3 G k n m s c u C t z a; have hq:‖q'‖ ≤ ‖T‖:= ((ear3 j' h ht hc he hv hx hp p y).trans (le_max_left ..)).trans (Real.le_norm_self _); have hs:0 ≤ A*‖T‖:= mul_nonneg ha (norm_nonneg _); have hF:0≤ F:= add_nonneg (Win_hi ..) (Win_hi ..); by_cases hr:D≤16*M
         · have hh':‖b*q'‖ ≤ A*‖T‖*(burst μ' B*burst μ' B'):=by rw [burst, burst,←Real.exp_add,← mul_add]; exact swayPay hF ht h.vein.warmth ha hh hq
           exact hh'.trans (mul_le_mul_of_nonneg_left (mul_le_mul (on_J x z' p ((le_max_left ..).trans hr)) (on_J x Z y ((le_max_right ..).trans hr)) (Real.exp_nonneg _) (add_nonneg (wake ..) (unt_J ..))) hs)
         have hy : ‖b*q'‖≤ A*‖T‖*Real.exp (-μ'*(d+d'+(B+B'))):= Norm_K hF ht h.vein.warmth ha hh (by linarith only [le_max_left d d',le_max_right d d']) (show 0 < D from (by have h':0≤ (M:ℝ):=Nat.cast_nonneg _;linarith only[h',not_le.mp hr])) hq (fun H => (TallB x j' h ht hc he hv hx hX hp (Nat.cast_nonneg M) p y _ _ rfl (not_le.mp hr) H).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (Real.le_norm_self _)) (Real.exp_nonneg _)))
         apply hy.trans; apply mul_le_mul_of_nonneg_left _ hs; apply le_trans _ (mul_le_mul (le_add_of_nonneg_right (unt_J x z' p)) (le_add_of_nonneg_right (unt_J x Z y)) (wake ..) (add_nonneg (wake ..) (unt_J ..))); unfold wigP burst; rw [mul_add,mul_add,mul_add,Real.exp_add,Real.exp_add,Real.exp_add]; unfold d d' B B'; ring_nf; exact le_rfl
end
end YM.OPE.Borealis.Galea
