import YM.FormalOPE.RG10.MultiGauge.Loom
/-!
 # pinching multi-polynomial cylinders through a genuine Schur step with explicit arguments
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory Measure PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F K : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F]
 [NormedAddCommGroup K][NormedSpace ℝ K][FiniteDimensional ℝ K][MeasurableSpace K][BorelSpace K]
namespace Splice
open Papers PowerSeries
variable (Λ:Law E)(d:(F × K) ≃ₗ[ℝ] E)
variable (μ:Measure E)[IsAddHaarMeasure μ](ν : Measure F)[IsAddHaarMeasure ν] (ρ : Measure K)[IsAddHaarMeasure ρ]
 def partialMean : Permit E →ₗ[ℝ] Permit K:= (splitting (fast Λ d) ν).comp (translation (fusion Λ d).toLinearMap).toLinearMap
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] μ [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℝ K] ρ in
@[simp] lemma restores : partialMean Λ d ν 1=1:= by change splitting (fast Λ d) ν (translation _ 1)=1; rw [map_one,singly]
lemma newborn (x:Permit E) : opening μ Λ x = opening ρ (rest Λ d) (partialMean Λ d ν x):= by
 change Λ.average μ x.val= _; rw [show Λ.average μ x.val= _ from splice_int Λ d μ ν ρ _ (useful μ Λ x)]; -- lean?
 change (rest Λ d).average _ _=(rest Λ d).average _ (splitting _ _ _).val
 rw [funext (Penn (fast Λ d) ν _)]; rfl

-- lift to full coefficients, invert *full* conditional normalization before removing.
 def throughPrice {S T:Type}[CommRing S][CommRing T](f:S→+ T): PowerSeries S →+ PowerSeries T where
  toFun A := PowerSeries.mk (fun i=> f (coeff i A))
  map_add' x y := by ext i; simp
  map_zero':= by ext i; simp
omit Λ d μ ν ρ in -- env not needed?
lemma keepsThrough {S T:Type}[CommRing S][CommRing T](f:S→+ T){u v: PowerSeries S}{n}(h: Through n u v): Through n (throughPrice f u) (throughPrice f v) := fun i hi=> by simp [throughPrice,h i hi]

abbrev Ticket (E: Type)[NormedAddCommGroup E][NormedSpace ℝ E]:= PowerSeries (Permit E)
 def reclose : Ticket E→+ Ticket K:= throughPrice (partialMean Λ d ν).toAddMonoidHom
 def input : Ticket E→+ PowerSeries ℝ := throughPrice (opening μ Λ).toAddMonoidHom
 def incline (a:Ticket E):= constantCoeff a=1
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] μ [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℝ K] ρ in
lemma born_transfer {P:Ticket E}(hp:incline P): incline (reclose Λ d ν P):= by
 unfold incline reclose throughPrice; rw [← coeff_zero_eq_constantCoeff_apply ..]; unfold incline at hp; simp [hp]; -- probably coeff zero -> constant dp
lemma underBudget {P:Ticket E} (hp: incline P): constantCoeff (input Λ μ P)=1:= by
 unfold incline at hp; simp [hp,input,throughPrice,starts]
lemma allAhead (P:Ticket E) : input Λ μ P=input (rest Λ d) ρ (reclose Λ d ν P):= by apply PowerSeries.ext; intro i; unfold input reclose throughPrice; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe]; exact newborn ..

-- version always preserves quotient when dividing by full unmarked weight
 def enjoy (P W:Ticket E) := input Λ μ (W*P) * (input Λ μ W)⁻¹
 def delivered (P W:Ticket E):Ticket K:= reclose Λ d ν (W*P) * PowerSeries.invOfUnit (reclose Λ d ν W) 1
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] μ [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℝ K] ρ in
lemma junior (P : Ticket E){W:Ticket E}(hp:incline W): reclose Λ d ν W * delivered Λ d ν P W = reclose Λ d ν (W*P) := by unfold delivered; rw [mul_comm (reclose Λ d ν W),mul_assoc,invOfUnit_mul (reclose Λ d ν W) 1 (born_transfer Λ d ν hp),mul_one]
lemma preserve (P : Ticket E){W:Ticket E}(hp: incline W): enjoy Λ μ P W=enjoy (rest Λ d) ρ (delivered Λ d ν P W) (reclose Λ d ν W) := by unfold enjoy; rw [junior Λ d ν P hp,allAhead Λ d μ ν ρ W,allAhead Λ d μ ν ρ (W*P)]
end Splice
end YM.FormalOPE.RG10.MultiGauge
