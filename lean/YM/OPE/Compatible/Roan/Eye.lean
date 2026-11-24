import YM.OPE.Compatible.Roan.Peak
/-! # far protocol ternary. Accurate when either order.T -/
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
variable {L:Host K T} {q:Sender L} (p:Site L.f) (j:Phase) {Y:Studio L}{w:Bid.Dir G L.c}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "U!"=> RiseT G k s c u C t z a
local notation "Β!"=> Λ_B G k s c u C t z a
local notation "R!"=>fun i:ℕ=> Βuffs G s c C (roomV G i z)
local notation "G!"=> FWind G s c u C t
local notation "T!"=> Cσ G s c u C t
noncomputable def Alc (m n:ℕ)(U G:price)(C:ℕ→price) :ℝ:= max (telemetry.Bezel U (hikeP G m) (hikeP G n) (reelP G (C 0) m) (reelP G (C 0) n)) (telemetry.Garlic U (hikeP G n) (reelP G (C n) m))
noncomputable def Alps3 (m n:ℕ)(U A G t:price)(C:ℕ→price):= beacon (2* trioK (U 4) (hikeP G m 4) (hikeP G n 4)) (trioK (A 4) (hikeP G m 4) (hikeP G n 4)+trioK (reelP G t m 4) (U 4) (hikeP G n 4)+trioK (reelP G t n 4) (U 4) (hikeP G m 4)) (2* max (Alc m n U G C) (Alc n m U G C))
noncomputable abbrev Yeast (G:Gauge)(k m n:ℕ)(s c u C t z a:ℝ):= Alps3 m n (RiseT G k s c u C t z a) (Λ_B G k s c u C t z a) (FWind G s c u C t) (Cσ G s c u C t) (fun i=>Βuffs G s c C (roomV G i z))
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)(hw:‖w‖≤ t)(hA:ReserveQ L p Y w ℓ)
variable {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L p X ℓ)(hp:Funded L X q a k)(hr:0 ≤ ℓ)
include h ht hc he hv hx hX hp hr
lemma Bloat (x:RodZ L m)(y:RodZ L n)(z' z'':Site L.f)
        (hR:16*ℓ < Dtn p z') (_hD:Dtn p z''≤ Dtn p z')(ht':Inrange L z' x+Inrange L z'' y ≤ Dtn p z'/32) : ‖Wish3 L q Y j x y‖≤ Alc m n U! G! (R!)* Real.exp (-(u*(Dtn p z'/8))):=by
              let D:= Dtn p z'; have hl:= Win_hi L z' x; have hL:= Win_hi L z'' y
              have hv₀(i): D*(3/4:ℝ)+D/8 ≤ Dtn p (Wct L (x i)):=by
                   have hv:=Dtn_tag p (Wct L (x i)) z'; rw [DtCom (Wct L (x i)) z'] at hv; unfold D; linarith only[hL,hR,hr,ht', Win_go L z' x i,hv]
              by_cases hS:Dtn p z''≤ D/2
              · have hν(i): Dtn p (Wct L (y i))≤ D*(3/4:ℝ) :=by apply le_trans (Dtn_tag p z'' (Wct L (y i))); unfold D at *; linarith only[Win_go L z'' y i,ht',hl,hR,hr,hS] -- shadow he
                have hj:Training L p X (D*(3/4)):=fun i hi=> (hX i hi).trans (by unfold D; linarith only [hR,hr]); apply (Thus p j h ht hc he hv hx hj hp x y hv₀ hν).trans; exact mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_nonneg _)
              have hu(i): ℓ+D/8 ≤ Dtn p (Wct L (y i)):=by have hp:= Dtn_tag p (Wct L (y i)) z''; rw [DtCom (Wct L (y i)) z''] at hp; unfold D at *; linarith only [Win_go L z'' y i,ht', hp,not_le.mp hS,hR,hl,hr]
              have hX'(i:Fin m): ℓ+D/8 ≤ Dtn p (Wct L (x i)):= (le_trans (by unfold D; linarith only[hR,hr]) (hv₀ i)); exact (aCross p j h ht hc he hv hx hX hp x y hX' hu).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_nonneg _))
lemma TallB (x:RodZ L m)(y:RodZ L n)(z' z'':Site L.f) (hR:R=max (Dtn p z') (Dtn p z'')) (ht':16*ℓ< R)(hp': Inrange L z' x+Inrange L z'' y≤ R/32): ‖Wish3 L q Y j x y‖ ≤ max (Alc m n U! G! (R!)) (Alc n m U! G! (R!))*Real.exp (-(u*(R/8))):=by
           rcases le_total (Dtn p z') (Dtn p z'') with hh|hh
           · rw[max_eq_right hh] at hR; subst R; rw [Wish3,(Order3 Y.μφ _ _ _).1]; exact (Bloat p j h ht hc he hv hx hX hp hr y x z'' z' ht' hh ((add_comm ..).trans_le hp')).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_nonneg _))
           rw [max_eq_left hh] at hR;subst R; exact (Bloat p j h ht hc he hv hx hX hp hr x y z' z'' ht' hh hp').trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_nonneg _))
include hw hA
local notation "W!"=> worldA L w
lemma Fares(x:RodZ L m)(y:RodZ L n)(z' z'':Site L.f) : Pulses (Wish3 L q Y j x y-Wish3 L q W! j x y) (max (Dtn p z') (Dtn p z'')) (Inrange L z' x+ Inrange L z'' y) ℓ (Yeast G k m n s c u C t z a) u:=by
         let f:= U!; let b:= G!; let R:= (R!); let B:= max (Alc m n U! G! R) (Alc n m U! G! R); obtain ⟨hP,hL,hU⟩:=beacons (2*trioK (U! 4) (hikeP G! m 4) (hikeP G! n 4)) (trioK (Β! 4) (hikeP b m 4) (hikeP b n 4)+ trioK (reelP b T! m 4) (U! 4) (hikeP b n 4)+trioK (reelP b T! n 4) (U! 4) (hikeP b m 4)) (2*B); have hf:Scale W! t:= grantW hw; refine ⟨(norm_sub_le ..).trans ((add_le_add (ear3 j h ht hc he hv hx hp x y) (ear3 j h ht hc he hf hx hp x y)).trans ((two_mul ..).symm.trans_le hP)),fun hx' hy=>?_,fun hy hz=>?_⟩
         · have hg(i:Rubric G X): Rebound L Y w ℓ (Sum.inr (shout G X i)):=hides L p Y w hA hr _ (le_trans (hX (shout G X i) i.1.property) (by linarith only[hr])); apply (Cent3 j h ht hc he hv hx hp hw hg x y ?_ ?_).trans (mul_le_mul_of_nonneg_right hL (Real.exp_nonneg _)); exact lapNear p hA hr z' x ((le_max_left ..).trans hx') ((le_add_of_nonneg_right (Win_hi ..)).trans hy); exact lapNear p hA hr z'' y ((le_max_right ..).trans hx') ((le_add_of_nonneg_left (Win_hi ..)).trans hy)
         exact (norm_sub_le ..).trans ((add_le_add (TallB p j h ht hc he hv hx hX hp hr x y z' z'' rfl hy hz) (TallB p j h ht hc he hf hx hX hp hr x y z' z'' rfl hy hz)).trans ((by rw [←two_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hU (Real.exp_nonneg _))))
end
end YM.OPE.Borealis.Galea
