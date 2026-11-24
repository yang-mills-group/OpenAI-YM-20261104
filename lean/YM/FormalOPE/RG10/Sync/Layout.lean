import YM.FormalOPE.RG10.Sync.Pattern
/-!
 # Projection of an actual Chart average against a polynomial ticket to the
     finite row grammar. Covariances assigned by inverse of supplied Law.
     Costs need pricing on these real diagnostics, even after complex adaptation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {E F K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 [FiniteDimensional ℝ F] [MeasurableSpace F][BorelSpace F] [NormedAddCommGroup K][NormedSpace ℝ K]
variable (Γ: Law F)
variable {I B:Type}[Fintype I] [Fintype B]
variable (L:Layout I E)(Q: Layout B K) (d:F→ₗ[ℝ] E)
variable (ν:Measure F)[Measure.IsAddHaarMeasure ν]
local notation "σ"=> Row (Space F)
 def matrix (a:I)(i:Space F):= L (d (bank Γ i)) a
local notation "q"=> matrix Γ L d
local notation "P"=> across L Q
omit [MeasurableSpace F] [BorelSpace F] [Fintype I] in
lemma entered (x:σ): alongFine q x= tint L (d (pave Γ x)):= funext fun i=> congr_arg Complex.ofReal (repr Γ ((feature L i).comp d) x).symm
omit [MeasurableSpace F] [BorelSpace F] [Fintype I] in
lemma matrix_match (i j:I): crossed (q i) (q j)=Γ.wick ((feature L i).comp d) ((feature L j).comp d):= (dual Γ ((feature L i).comp d) ((feature L j).comp d)).symm

 def accompany (d : F→ₗ[ℝ] E): F × K →ₗ[ℝ] E × K:= d.prodMap LinearMap.id
local notation "D"=> accompany (K:=K) d
local notation "P₀"=> translation (accompany (K:=K) d)

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
lemma actor (u: Joins.Gauss.hall (Space F)): Bulk.mean u=∫ x:σ, u.val ((),x) ∂standard (Space F):= by
 unfold Bulk.mean FlatFeed.mean; simp only [LinearMap.coe_mk,AddHom.coe_mk]; simp [Joins.Gauss.standardFeed]
lemma consumes (a:Permit (E×K)): Bulk.hand q (ink P a) = ink Q (splitting Γ ν (P₀ a)):= by
 apply recognise Q; intro y; rw [Bulk.hand_eq,actor (F:=F),expresses,Penn,acceptance,← integral_complex_ofReal]; refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun i =>?_)
 dsimp only [study_apply]; -- eq
 rw [study_apply,entered,←colored,expresses]; rfl
 def simpleMean : Ticket (F × K)→+ Ticket K:= throughPrice (splitting Γ ν).toAddMonoidHom
lemma moving (W:Ticket (E×K)): Bulk.move q (digital P W)= digital Q (simpleMean Γ ν (boost D W)):= by
 apply PowerSeries.ext; intro i; rw [Bulk.move,coeff_mk]; simp_rw [digital, PowerSeries.coeff_map,simpleMean, boost, throughPrice,AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe]; exact consumes Γ L Q d ν _
lemma simply {W:Ticket (F×K)}(h: incline W): incline (simpleMean Γ ν W):= by unfold incline simpleMean throughPrice; rw [←coeff_zero_eq_constantCoeff_apply]; unfold incline at h; simp [h,singly]

end YM.FormalOPE.RG10.Sync
