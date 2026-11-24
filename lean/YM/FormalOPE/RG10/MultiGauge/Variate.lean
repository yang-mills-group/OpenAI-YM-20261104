import YM.FormalOPE.RG10.MultiGauge.Engine
/-!
 # λ receipts printed prior to mean evaluation
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
namespace Stack
open PowerSeries Papers Splice StationaryMarks
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {G:Gauge} {I J:Type}[Fintype I][Fintype J]
variable (U:Survey G I J) (P:ChartRatio G)
local notation "Z"=> Direction G I

 def imbed (O:Spending G I): Ticket Z:= rise (O ∘ expLinks G I)
lemma label_mul {O F:Spending G I}(ho:Curtain O)(hf:Curtain F): imbed (O * F)= imbed O * imbed F:= rise_mul ho.germ hf.germ
lemma label_one : imbed (1:Spending G I)=1:= rise_one
lemma label_prod {X:Type}(s:Finset X)(c:X→Spending G I)(h:∀ i∈s,Curtain (c i)): imbed (∏ i∈s,c i)=∏ i∈s,imbed (c i):= by
 induction s using Finset.induction with
 | empty=> simp [label_one]
 | insert=>
   rename_i a s hi ih; simp only [Finset.prod_insert hi]; have hh:∀ i∈s,Curtain (c i):= fun i hj=> h i (by simp [hj]); rw [label_mul (h a (by simp)) (Curtain.gather _ _ hh),ih hh]
-- unscheduled exponential base (no Obs). Weight-only as chosen by Camera
 def planting : Ticket Z:= rise (jacobian P) * exponential (advancing (U.target ∘ expLinks G I))
 def spikeCost (i:J):Ticket Z:= drop 1 (imbed (U.field i))
 def dressing : Ticket Z:= ∑ i:J, carry (Tracks.shadow (U.w i))*spikeCost U i
 def tagMass {k:ℕ}(i: Fin k→J): Ticket Z:= ∏ j:Fin k, spikeCost U (i j)
lemma spikeBack (H:U.Ready)(i:J): X * spikeCost U i=imbed (U.field i):= by
 unfold spikeCost; rw [←pow_one X]; apply recover; intro j hj; obtain rfl:j=0 := Nat.lt_one_iff.mp hj; unfold imbed rise; rw [PowerSeries.coeff_mk]; apply Subtype.ext; ext1 j; simp [(H.sincere _).center]
lemma spikeZero (H:U.Ready)(i:J): constantCoeff (spikeCost U i)=0:= by
 unfold spikeCost drop imbed rise; rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk,Nat.add_zero,coeff_mk]; apply Subtype.ext; exact funext (H.sincere i).centered.base1
lemma dressing_zero (H:U.Ready) : constantCoeff (dressing U)=0:= by simp_rw [dressing, map_sum,map_mul,spikeZero U H,mul_zero]; exact Finset.sum_const_zero
lemma spikeProduct (H:U.Ready){k:ℕ}(i:Fin k→ J): X^k * tagMass U i=imbed (∏ j: Fin k,U.field (i j)):= by
 rw [label_prod _ _ (fun j _ => H.localAll (i j)), tagMass]; simp_rw [←spikeBack U H]; simp [Finset.prod_mul_distrib]
lemma threshold (k:ℕ):
 (dressing U)^k=∑ e: Fin k→ J, carry (∏ i:Fin k,Tracks.shadow (U.w (e i))) * tagMass U e:= by
 unfold dressing; rw [Fintype.sum_pow]; refine Finset.sum_congr rfl fun _ _=>?_ ; rw [map_prod]; exact Finset.prod_mul_distrib
end Stack
end YM.FormalOPE.RG10.MultiGauge
