import YM.OPE.Compatible.Cum.Plays
/-!
# IPP at connected dots. invariant pencil placement unrestricted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter Set MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin
variable {E F I J R:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
local notation "W"=> E→ℝ
variable (p:I→E→ℝ) [DecidableEq I]
local notation "P"=> Finset I
def okP (p:I→E→ℝ)(s:P):Prop:= ∀ i∈s, Bond (p i)
def powr (p:I→E→ℝ) (s:P):W:= ∏ i∈s,p i
def drink (μ:Measure E)(L:Law E)(p:I→E→ℝ)(f:E→ℝ)(s:P):ℝ:= L.average μ (f*powr p s)
def Tap (μ:Measure E)(L:Law E)(p:I→E→ℝ)(f:E→ℝ):Finset I→ℝ:= Shell.Tab (drink μ L p 1) (drink μ L p f)
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma powrB (s:P)(h:okP p s): Bond (powr p s):=by
      induction s using Finset.induction_on with
      | empty=> simp [powr]
      | insert i s hi ih=> rw [powr,Finset.prod_insert hi]; exact (h i (mem_insert_self ..)).mul (ih fun j hj=>h j (mem_insert_of_mem hj))
omit [DecidableEq I] in
lemma sated : drink μ L p 1 ∅=1:=by unfold drink powr; rw [Finset.prod_empty, one_mul,L.empty]
lemma stated (q:W)(s:P):Con (Tap μ L p q) (drink μ L p 1) s=drink μ L p q s:=composite _ _ (sated μ L p) s
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
lemma salary (q:W) : Tap μ L p q ∅=L.average μ q:=by unfold Tap; rw [Tab_rec]; simp [drink,powr]
lemma penny (s:P):Tap μ L p 1 s=if s=∅ then 1 else 0:=by
    symm; apply agrees (q:=fun u:P=> if u=∅ then 1 else 0) _ _ (sated μ L p) s
    intro i hi; unfold Con; rw [sum_eq_single ∅]; · simp
    · intro j _ H;simp only [if_neg H,zero_mul]
    simp
lemma Tap_scale (f:W)(c:ℝ)(s:P): Tap μ L p (c • f) s=c* Tap μ L p f s:=by
     symm; apply agrees (q:=fun t:P=>c*Tap μ L p f t) _ _ (sated μ L p) s; intro j _; unfold Con; simp_rw [mul_assoc,←mul_sum]; rw [show _ * (∑ _∈_, _)= _ from congr_arg (c * · ) (stated μ L p f j)]; unfold drink; rw [smul_mul_assoc,scooted]
lemma Tap_merge (s:P)(h:okP p s)(a b:W)(hp:Bond a)(hx:Bond b): Tap μ L p (a+b) s=Tap μ L p a s+Tap μ L p b s:=by
     symm; apply agrees (q:=fun i:P=> Tap μ L p a i+Tap μ L p b i) _ _ (sated μ L p) s; intro i hi; unfold Con; simp_rw [add_mul,sum_add_distrib]; rw [← show ∀ (f:W), drink μ L p f i = ∑ _∈_,_ from fun f=>(stated μ L p f i).symm]; rw [show (∑ u∈i.powerset, Tap μ L p b u * _) = _ from stated μ L p b i]; unfold drink; rw [add_mul]; have hk : Bond (powr p i):=powrB p i fun j h'=> h _ (hi h'); exact (sun μ L (hp.mul hk) (hx.mul hk)).symm
lemma prices (s:P)(h:okP p s)(t:Finset J)(q:J→W)(hp:∀ i∈t,Bond (q i)): Tap μ L p (∑ i∈t,q i) s=∑ i∈t, Tap μ L p (q i) s:=by
     induction t using Finset.induction_on with
     | empty=> rw [sum_empty,sum_empty]; simpa only [zero_smul,zero_mul] using Tap_scale μ L p (fun _=>0) 0 s
     | insert i t hi ih=>rw [sum_insert hi,sum_insert hi,Tap_merge _ _ p s h _ _ (hp _ (mem_insert_self ..)) (show Bond (∑ j∈t,q j) from ?_), ih (fun i hi=> hp _ (mem_insert_of_mem hi))]; rw [show (∑ j∈t,q j)=fun x:E=>∑ j∈t,q j x from funext fun x=> sum_apply x ..]; exact Bond.sum q t (fun j hj=>hp _ (mem_insert_of_mem hj))
section
omit μ L [MeasurableSpace E][BorelSpace E]
variable (v:E)
def Raise (v:E)(x:W)(y:W): Prop:=∀ a:E,∀ t:ℝ,HasDerivAt (fun s:ℝ=>x (a+s • v)) (y (a+t • v)) t
-- all y-s constraints on v chosen
-- leg (ℓ=p* id)
end
variable (v:E)
lemma Query (a b:W)(A:I→W)(s:P)(hx:okP p s)(hy:okP A s)(ht:Bond a)(hf:Bond b)
     (hw:Raise v a b)(hp:∀ j∈s,Raise v (p j) (A j)):
     Tap μ L p ((L.P v)*a) s=Tap μ L p b s +∑ i∈s,Tap μ L p (A i*a) (s.erase i):=by
          let H(j:I):= Tap μ L p (A j*a)
          symm; apply agrees (q:=fun t:P=>Tap μ L p b t+∑ i∈t,H i (t.erase i)) _ _ (sated μ L p) s; intro j hj
          have HE:Con (fun t:P=>Tap μ L p b t+∑ i∈t,H i (t.erase i)) (drink μ L p 1) j= drink μ L p b j+∑ i∈j,drink μ L p (A i*a) (j.erase i):=by
             unfold Con; simp_rw [add_mul,sum_add_distrib]; rw [show (∑ i∈ j.powerset,Tap μ L p b i* _) = _ from stated μ L p b j]; apply congr_arg; exact (roses H _ _).trans (Finset.sum_congr rfl fun i _=> stated μ L p _ _)
          rw [HE]; let s':= powr p j; let q(i):=(A i * a)*powr p (j.erase i); let u:= b*s'+ ∑ i∈j,q i; have hS(i:P)(h:i⊆s):Bond (powr p i):=powrB p i fun k hK=>hx k (h hK); have hh(i)(hi:i ∈ j):Bond (q i):= ((hy i (hj hi)).mul ht).mul (hS _ (Finset.Subset.trans (erase_subset ..) hj))
          have hX: Bond (∑ i∈j,q i):=by rw [show (∑ i∈j,q i)=fun x:E=>∑ i∈j,q i x from funext fun x=>sum_apply x ..]; exact Bond.sum q j hh
          change L.average μ (b*s') + (∑ i∈j,L.average μ (q i))=L.average μ (⇑(L.P v)*a*s'); rw [mul_assoc,← science μ L j q hh,← sun μ L (hf.mul (hS _ hj)) hX]; symm; refine bask μ L v (a*s') u (ht.mul (hS _ hj)) ((hf.mul (hS _ hj)).add hX) ?_
          intro x t; let X:=x+t • v; let F:=∑ i∈j, powr p (j.erase i) X * A i X
          have hh':HasDerivAt (fun u:ℝ=>s' (x+u • v)) F t:=by
              unfold s' F powr; simp only [Finset.prod_apply]; exact HasDerivAt.fun_finsetProd (fun i hi=>hp i (hj hi) x t)
          convert! ((hw x t).mul hh') using 1; simp only [u,q,Pi.add_apply, Pi.mul_apply,Finset.sum_apply]; unfold F; rw [Finset.mul_sum]; apply congr_arg; exact Finset.sum_congr rfl fun _ _=>by unfold X;ring
end YM.OPE.Libra.Shell
