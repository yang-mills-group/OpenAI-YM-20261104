import YM.FormalOPE.RG10.Sync.Card
/-!
 # Rank of the pivot polynomial rises
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers MultiGauge.Stack
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp OpenSlots
open PertExtension Precision Inherit PertExtension.Series PertExtension.Series.Tested Radial Chart
open MvPolynomial (totalDegree C_mul' aeval)
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {I:Type}[Fintype I]
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable (L: Layout I E)
namespace stock
variable [FiniteDimensional ℝ E]
lemma headed (f:E→ℝ)(i:ℕ) : totalDegree (coeff i (digital L (rise f))) ≤ i:= by
 let D:= Module.finBasis ℝ E
 let a:= iteratedFDeriv ℝ i f 0
 let c (p:Fin i→Space E):= (↑i.factorial:ℝ)⁻¹ * a (fun j=>D (p j))
 let v (p:Fin i→ Space E): Packet I:= Complex.ofReal (c p) • ∏ j:Fin i, stroke L (D.coord (p j))
 have he (x:E): jet f i x = ∑ p:Fin i→Space E, c p*∏ j:Fin i, D.coord (p j) x:= by
   unfold jet; change _* a (fun _=> x)=_
   conv_lhs => rhs; rhs; intro; rw [← D.sum_repr x]
   rw [show a (fun _=> ∑ j:Space E,D.repr x j • D j)= _ from MultilinearMap.map_sum a.toMultilinearMap (fun _ j=> D.repr x j • D j), Finset.mul_sum]
   apply Finset.sum_congr rfl; intro p _;
   rw [show a.toMultilinearMap (fun j=> D.repr x (p j) • D (p j))= _ from a.toMultilinearMap.map_smul_univ ..]
   unfold c; change _ * (_*a _)= _ * (∏ j:Fin i, D.repr x (p j)); ring
 rw [only, show ink L _=∑ p,v p from ?_];
 · apply (MvPolynomial.totalDegree_finsetSum ..).trans (Finset.sup_le (fun p _=>?_)); unfold v; apply (MvPolynomial.totalDegree_smul_le ..).trans ((MvPolynomial.totalDegree_finsetProd ..).trans ?_); simpa using (Finset.sum_le_sum (s:= Finset.univ (α:=Fin i)) (fun j _=> linear_one L (D.coord (p j))))
 apply recognise L; intro x; rw [expresses, map_sum,rise,coeff_mk]; change (jet f i x:ℂ)=_
 rw [he,Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro p _; unfold v; simp only [map_smul,map_prod,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_prod]; -- inspect
   exact congr_arg ((↑(c p):ℂ)* ·) (Finset.prod_congr rfl (fun j _=> (stencil L (D.coord (p j)) x).symm))
lemma rising (f:E→ℝ): stock 0 (rise f):= by intro I H L r i hi; exact (headed L f i).trans (by omega)
omit [FiniteDimensional ℝ E] in
lemma carrying (x: PowerSeries ℝ): stock (E:=E) 0 (carry x):= by intro I H L r i hi; rw [only,carry, PowerSeries.coeff_map,currency,MvPolynomial.totalDegree_C]; omega
omit [FiniteDimensional ℝ E] in
lemma rolling (c:ℝ): stock 0 (roll (E:=E) c):= (show (carry (E:=E) (PowerSeries.C c))=roll c from PowerSeries.map_C ..) ▸ carrying (C c)
lemma issuable (f:E→ℝ): stock 0 (Stack.advancing f):= by
 intro I H L r i hi; rw [only]; by_cases h:i=0
 · subst i; rw [coeff_zero_eq_constantCoeff_apply, advancing_zero]; simp
 unfold Stack.advancing Stack.drop; rw [map_add,coeff_mk,map_neg,coeff_C,if_neg h,add_zero,map_neg, MvPolynomial.totalDegree_neg, ← only]; exact (headed ..).trans (by omega)
lemma owned (w:PowerSeries ℝ)(p:E→ℝ)(h: Stationary p): stock 0 (OpenSlots.chip w p):= by
 have he: stock 0 (Stack.drop 1 (rise p)):= by
    intro I H L r i hi; rw [only,Stack.drop,coeff_mk]; by_cases hr:i=0
    · subst i; rw [show coeff (1+0) (rise p)=0 from by unfold rise; rw [coeff_mk]; apply Subtype.ext; exact funext h.base1]; simp
    rw [← only]; exact (headed ..).trans (by omega)
 exact stock.exponential (add (show stock 0 _ from stock.mul (rolling _) (issuable p)) (show stock 0 _ from stock.mul (carrying _) he))
omit [Fintype I] in
lemma revived (G:Gauge)(P:ChartRatio G) (I:Type)[Fintype I]: stock 0 (tissue P I):= stock.mul (rolling _) (rising _)
end stock
end YM.FormalOPE.RG10.Sync
