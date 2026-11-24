import YM.FormalOPE.RG10.OpenSlots.Smooth
/-!
 # Separate chips for each fine or block pricing; legitimate before amputation
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {E K: Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [NormedAddCommGroup K][NormedSpace ℝ K][FiniteDimensional ℝ K]
 def pay (w:PowerSeries ℝ)(p:E→ℝ): Ticket E:= roll (term w 0) * advancing p + carry (Tracks.shadow w) * Stack.drop 1 (rise p)
 def chip (w:PowerSeries ℝ)(p:E→ℝ) : Ticket E:= exponential (pay w p) -- exponent arg should have degree≥1
lemma stipend (w:PowerSeries ℝ)(p:E→ℝ)(h:Stationary p): constantCoeff (pay w p)=0:= by
 unfold pay; rw [map_add,map_mul,map_mul, advancing_zero, mul_zero, show constantCoeff (Stack.drop 1 (rise p))=0 from ?_,mul_zero,zero_add];
 apply Subtype.ext; ext1 x; rw [←coeff_zero_eq_constantCoeff_apply,Stack.drop,coeff_mk,Nat.add_zero, rise,coeff_mk]; exact h.base1 x
lemma restores (w:PowerSeries ℝ)(p:E→ℝ): incline (chip w p):= initial _

lemma advanced_lift (d:K→ₗ[ℝ] E)(p:E→ℝ)(h:ContDiffAt ℝ ω p 0): boost d (advancing p)=advancing (p ∘ d):= by
 unfold advancing; rw [map_add, ←Vault.climbing d (h.of_le le_top), ← _root_.map_neg]; congr 1
 simp [boost]
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ K] in
lemma still_c (d:K→ₗ[ℝ] E) (A:PowerSeries ℝ): boost d (carry A)=carry A:= by apply into; intro; simp only [caught,load]
lemma pullPay (d:K→ₗ[ℝ] E)(w:PowerSeries ℝ)(p:E→ℝ)(h:ContDiffAt ℝ ω p 0): boost d (chip w p)=chip w (p∘d):= by
 unfold chip pay; rw [boost_exp,map_add,map_mul,map_mul,advanced_lift d p h, still_c,←Vault.climbing d (h.of_le le_top)]
 rw [show boost d (roll (term w 0)) = _ from (show boost d (roll (term w 0))=roll (term w 0) from by apply into; intro; simp only [caught,rollThrough]), show boost d (Stack.drop 1 (rise p))=Stack.drop 1 (boost d (rise p)) from ?_]; unfold boost Stack.drop; apply PowerSeries.ext; intro i; simp

omit [FiniteDimensional ℝ E] in
lemma jetSum {α:Type}(s:Finset α)(u:α→ℝ)(V:α→E→ℝ) (h:∀ i,ContDiffAt ℝ ω (V i) 0)(i:ℕ)(x:E):
    jet (∑ a∈s,u a • V a) i x=∑ a∈s,u a * jet (V a) i x:= by
 induction s using Finset.induction with
 | empty=>
   simp only [Finset.sum_empty]; cases i with
   | zero => exact jet_zero (0:E→ℝ) _
   | succ i=> simp [jet,show (0:E→ℝ)= fun _=>0 from rfl,iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]
 | insert a s hz ih=> rw [Finset.sum_insert hz, Finset.sum_insert hz, Inherit.plus (a:=u a • V a) (b:=∑ i∈s,u i • V i) i ((h a).const_smul (u a)) (by
       rw [show ∑ i ∈ s,u i • V i = fun x=> ∑ i∈s,(u i • V i) x from funext (fun x=> Finset.sum_apply ..)]; exact ContDiffAt.sum (fun i _=> (h i).const_smul (u i))), ih, Inherit.times i (u a) (h a)]
lemma advance_jets {α:Type}(s:Finset α)(u:α→ℝ)(V:α→E→ℝ) (h:∀ i,ContDiffAt ℝ ω (V i) 0):
 advancing (∑ a∈s,u a • V a)=∑ a∈s,roll (u a) * advancing (V a):= by
 apply into; intro x; apply PowerSeries.ext; intro i; rw [map_sum]; simp_rw [_root_.map_mul,map_sum,rollThrough,coeff_C_mul,levels]; unfold Radial.layers; by_cases hi:i=0
 · simp [hi]
 simp [hi,jetSum s u V h,Finset.sum_neg_distrib]
omit [FiniteDimensional ℝ E] in
lemma compose_two (u v:Ticket E)(h:constantCoeff u=0)(g:constantCoeff v=0): exponential (u+v)=exponential u * exponential v:= by apply into; intro i; rw [_root_.map_mul,exponent,exponent,exponent,map_add,Formal.multispecies (RingHom.id _) (wrap h i) (wrap g i)]
omit [FiniteDimensional ℝ E] in
lemma compose_many {α:Type}(s:Finset α)(u:α→ Ticket E) (h:∀ i,constantCoeff (u i)=0): exponential (∑ a∈s,u a)=∏ a∈s,exponential (u a):= by
 induction s using Finset.induction with
 | empty=>
   rw [Finset.sum_empty,Finset.prod_empty]; apply PowerSeries.ext; intro i
   have he:= Stack.acting (E:=E) (A:=0) (map_zero _) i i le_rfl; rw [he]
   have hi (k:ℕ)(hk:k≠0): roll ((k.factorial:ℝ)⁻¹)*(0:Ticket E)^k=0:=by simp [hk]
   rw [Finset.sum_eq_single_of_mem 0 (by simp) (fun k _ h=>hi k h)]; simp [roll]
 | insert i s hz ih=> rw [Finset.sum_insert hz, Finset.prod_insert hz, compose_two _ _ (h i) (by simp [h]),ih]

-- merge formula includes unperturbed and schedule perturbation clocks
variable {I J:Type}[Fintype I][Fintype J]{U:Survey G I J}
local notation "Ξ"=> Direction G I
lemma toll_all (H:U.Ready): advancing (U.target ∘ expLinks G I) + dressing U=
 ∑ i, pay (U.w i) (U.field i ∘ expLinks G I):= by
 simp_rw [pay,Finset.sum_add_distrib]
 rw [show U.target ∘ expLinks G I=∑ i,term (U.w i) 0 • (U.field i∘ expLinks G I) from funext fun x=> by rw [Finset.sum_apply]; rfl, advance_jets Finset.univ (fun i=>term (U.w i) 0) (fun i=> U.field i ∘ expLinks G I) (fun i=> (H.sincere i).smooth)] -- dress equality
 rfl

 def tissue (P:ChartRatio G)(I:Type)[Fintype I]: Ticket (Direction G I):= roll ((jacobian P (0: Direction G I))⁻¹)* rise (jacobian P)
lemma awake {P:ChartRatio G}(H:LocalRatio P): incline (tissue P I):= by
 unfold incline tissue roll; have he:0<overhead P I:= official H; rw [map_mul,constantCoeff_C]; apply Subtype.ext; ext1 x; change (overhead P I)⁻¹ * ((constantCoeff (rise (jacobian P (U:=I)))).val x)=1; rw [←coeff_zero_eq_constantCoeff_apply, rise,coeff_mk]; change _*jet _ 0 x=1; rw [jet_zero]; exact inv_mul_cancel₀ he.ne'
lemma weight (H:U.Ready)(P:ChartRatio G) : Stack.weight P U=tissue P I * ∏ i, chip (U.w i) (U.field i ∘ expLinks G I):= by
 unfold Stack.weight planting tissue chip; rw [← compose_many _ _ (fun i=> stipend _ _ (H.sincere i).centered), ← toll_all H]; rw [compose_two _ _ (advancing_zero _) (dressing_zero U H)]; ring
end YM.FormalOPE.RG10.OpenSlots
