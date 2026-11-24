import YM.FVA2.Facade.Lift
/-!
# Splice open tickets in the unmasked realization

Off-line not just at eventual chosen truss. Evaluator takes point of the FULL open
field. Incline required when trying to sell AFTER division by complete conditional mass;
lemma at processor applies before division and claims no analytic property. Same
coordinate seed in both numerator/denominator, and initial coefficients through every
fixed stencil product (not pulling one mark separately and multiplying).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries
open MultiGauge Splice Papers Quadratic MultiGauge.Stack MarkovChain Warp
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {E F B Y K:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup B][NormedSpace ℝ B]
 [NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup K][NormedSpace ℝ K]

lemma tagThrough {S T:Type}[CommRing S][CommRing T](f:S→+ T)(A:PowerSeries S)(i:ℕ): coeff i (throughPrice f A)=f (coeff i A):= by unfold throughPrice; simp

section
variable {M N:Type}[NormedAddCommGroup M][NormedSpace ℝ M][NormedAddCommGroup N][NormedSpace ℝ N]
variable [FiniteDimensional ℝ M] [MeasurableSpace M][BorelSpace M](a : Quadratic (M×N))(ha:(core a).RespectsPrice)
variable (ν:Measure M)[ν.IsAddHaarMeasure]
lemma uptime (p:Ticket (M×N))(i:ℕ)(y:N): coeff i (Stack.read y (uptake a ν ha p))= ha.inner.average ν (fun u=>coeff i (Stack.read (u+skew a ha y,y) p)):= by
 rw [reading_term,uptake, tagThrough]; simp_rw [reading_term]; exact integrateP_display a ν ha _ _
-- lifts ticket with affine y relation. Useful when performing Stamp in equivalent Germ and leading y fixed.
 def hold (y:N): Ticket (M × N)→+*Ticket M:= (boost (LinearMap.inl ℝ M N)).comp (PowerSeries.map (Papers.relocate (LinearMap.id (R:=ℝ)) (skew a ha y,y)).toRingHom)
lemma held (p:Ticket (M×N))(y:N)(x:M): Stack.read x (hold a ha y p)= Stack.read (x+skew a ha y,y) p:= by
 unfold hold; rw [RingHom.comp_apply,caught]; apply PowerSeries.ext; intro i;
 rw [reading_term,coeff_map,reading_term]; change (coeff i p).val ((x,0)+(skew a ha y,y))=_; simp
lemma upton (p:Ticket (M×N))(y:N): Stack.read y (uptake a ν ha p)=input ha.inner ν (hold a ha y p):= by
 apply PowerSeries.ext; intro i; rw [uptime,input, tagThrough]; change _= ha.inner.average ν _; rw [←show (fun x:M=> coeff i (Stack.read (x+skew a ha y,y) p))=(coeff i (hold a ha y p)).val from funext fun x=>by rw [←held,reading_term]]
end

variable (e : (F×B)≃ₗ[ℝ] E) (π:(B×Y)→ₗ[ℝ] K) (a:Quadratic (E×Y)) (b:Quadratic (B×Y))
variable (q:Quadratic (F×K))
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F][FiniteDimensional ℝ B]
variable (hq:(core q).RespectsPrice)(ha:(core a).RespectsPrice)(hb:(core b).RespectsPrice)
local notation "χ"=> (skew q hq) ∘ₗ π
namespace Charged
variable {e π a b q} (h:Charged e (core q) a b ((skew q hq) ∘ₗ π))
variable {p:Ticket (E×Y)}{f: Ticket (F×K)}{g:Ticket (B×Y)}
variable [MeasurableSpace F][BorelSpace F][MeasurableSpace E][BorelSpace E][MeasurableSpace B][BorelSpace B]
variable (μ:Measure F)[μ.IsAddHaarMeasure](ν:Measure E)[ν.IsAddHaarMeasure](ρ: Measure B)[ρ.IsAddHaarMeasure]
include h μ ν ρ
local notation "d"=> pulley e χ
-- Sales processor identity with full Θ, no analytic estimate here. Don't need incline here.
theorem process (V:∀ x w y, Stack.read (e (x,w),y) p=Stack.read (x,π (w,y)) f * Stack.read (w,y) g) :
    uptake a ν ha p = uptake b ρ hb (boost π (uptake q μ hq f)* g) := by
 apply Stack.into; intro y; apply PowerSeries.ext; intro i
 let z := fun w:B=> w+skew b hb y
 let s:= boost π (uptake q μ hq f)*g
 rw [upton a ha ν, input,tagThrough,uptime]
 let A:= coeff i (hold a ha y p)
 change ha.inner.average ν A.val = hb.inner.average ρ fun u=> coeff i (Stack.read (z u,y) s)
 rw [show ha.inner.average ν A.val= _ from h.paid hq hb ha μ ν ρ A]
 apply congr_arg (hb.inner.average ρ); funext w;
 let B₀:=π (z w,y); let K₀:= hold q hq B₀ f
 let X: Ticket F:= K₀ * carry (Stack.read (z w,y) g)
 have ht (x:F) : A.val ((d) (x,w)) = (coeff i X).val x := by
     unfold A X K₀ B₀
     rw [←reading_term,held,h.centerQ hb ha,anchor_spend,V (x+χ (z w,y)) (z w) y]
     simp only [←reading_term, map_mul, held,load, ←reading_term]; rfl
 rw [funext ht]
 change opening μ hq.inner (coeff i X) = coeff i (Stack.read (z w,y) s)
 unfold X s; rw [map_mul (Stack.read _), caught, upton q hq μ, coeff_mul,coeff_mul, map_sum]; apply Finset.sum_congr rfl; intro j _
 rw [input, tagThrough];
 have hx (S:PowerSeries ℝ) (a:Permit F) (i:ℕ): a*coeff i (carry S)=(coeff i S) • a:= by unfold carry; rw [coeff_map]; rw [mul_comm, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,one_mul]
 rw [hx, map_smul]; exact mul_comm ..
end Charged
end YM.FVA2.Facade
