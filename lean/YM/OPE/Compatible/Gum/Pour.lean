import YM.OPE.Compatible.Gum.Kind
/-!
# Normalized and centered receipts pushed by finite ink.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
local notation "W"=> ScriptJ E
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma Bstar (c:Token) : ScriptJ.B (fun _ : E=>c):=fun _=> Bond.keep _
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma teamB (s:Finset I)(f:I → ScriptJ E)(h:∀ i∈s, ScriptJ.B (f i)): ScriptJ.B (∑ i∈s,f i):=by
      induction s using Finset.induction_on with
      | empty=>rw [Finset.sum_empty]; exact Bstar 0
      | insert i s hi ih=>rw [Finset.sum_insert hi]; exact ScriptJ.key (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma fairSum (w: W)(hw:w.B)(s:Finset I)(f:I→ ScriptJ E)(h:∀ i∈s, ScriptJ.B (f i)):fair μ L w (∑ i∈s,f i)=∑ i∈s, fair μ L w (f i):=by
    induction s using Finset.induction_on with
    | empty=>rw [sum_empty,sum_empty]; simpa using! (coin_F μ L (c:=0) _ 0 (Bstar 0) hw)
    | insert i s hi ih=>rw [sum_insert hi,sum_insert hi,Firmly μ L w hw (h i (mem_insert_self ..)) (teamB _ f (fun j hj=> h j (mem_insert_of_mem hj))),ih fun j hj=> h j (mem_insert_of_mem hj)]
variable (p:Ask→ E→ℝ)(hp:p 0=p 1)(hs:∀ i,Bond (p i))
def Conf (q: W)(i:Fin 3):Token:=Ū^i.val *rich (Tap μ L p (lumps q i))
omit μ L
protected def stripe (q:E→Token)(i:Fin 3): E→Token := fun x=>Ū^i.val * coin (lumps q i x)
include μ L
omit μ L [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma stroll (q:W)(h:q.B)(i:Fin 3): ScriptJ.B (Shell.stripe q i):=ScriptJ.height (Bstar _) (sty _ (h _))
include hp hs
lemma fairConf (q:W)(hq:q.B)(i:Fin 3): fair μ L (Stell p) (Shell.stripe q i)= Conf μ L p q i:=by unfold Conf Shell.stripe; rw [coin_F _ _ _ (Stell p) (fun x=> coin (lumps q i x)) (sty _ (hq _)) (bondW _ _ _ (hs _) (hs _) (hs _)),rootC μ L p hp hs _ (hq _)]
lemma bumper (q:W)(hq:q.B): fair μ L (Stell p) q=∑ i:Fin 3, Conf μ L p q i:=by nth_rw 1 [show q=∑ i:Fin 3,Shell.stripe q i from lumpSum q]; rw [show fair μ L (Stell p) _= _ from fairSum μ L (Stell p) (bondW _ _ _ (hs _) (hs _) (hs _)) Finset.univ _ fun i _=>stroll q hq i]; exact Finset.sum_congr rfl fun i _=>fairConf μ L p hp hs q hq i
def Cox (q y:W)(i j:Fin 3):Token:=Ū^(i.val+j.val)*rich (fun s=> πc μ L s p (lumps q i) (lumps y j) 4)
lemma fairCox (q y:W)(hq:q.B)(hy:y.B)(i j:Fin 3): fair μ L (Stell p) (Shell.stripe q i * Shell.stripe y j)=Cox μ L p q y i j+ Conf μ L p q i * Conf μ L p y j:=by
      let A:= Stell p; let V:=Shell.stripe q i; let X:= Shell.stripe y j; rw [← fairConf μ L p hp hs q hq i, ←fairConf μ L p hp hs y hy j]; let a(x:E):=coin (lumps q i x); let b(x:E):=coin (lumps y j x); let u:=Ū^i.val; let v:=Ū^j.val; have hp':ScriptJ.B a:=sty _ (hq _); have h':ScriptJ.B b:=sty _ (hy _); have hw:ScriptJ.B A:= bondW _ _ _ (hs _) (hs _) (hs _)
      change fair μ L A (V*X)= _ +fair μ L A V * fair μ L A X
      rw [show V*X=fun i=> (u*v)*((a*b) i) from funext fun x=> by change u*a x*(v*b x)=(u*v)*(a x*b x);ring,coin_F μ L (u*v) A (a*b) (ScriptJ.height hp' h') hw,show fair μ L A V=u* fair μ L A a from coin_F μ L u A a hp' hw, show fair μ L A X=v*fair μ L A b from coin_F μ L v A b h' hw, Cox,pow_add,← βpair μ L p hp hs _ _ (hq _) (hy _)]; change _= u*v*(fair μ L A (a*b)-fair μ L A a*fair μ L A b)+ _;ring
lemma centered (q y:W)(hq:q.B)(hy:y.B): fair μ L (Stell p) (q*y)- fair μ L (Stell p) q * fair μ L (Stell p) y=∑ i:Fin 3,∑ j: Fin 3, Cox μ L p q y i j:=by
     let A:=Stell p; let T:=fair μ L A; let X:=Shell.stripe q; let Y:= Shell.stripe y; have hp':ScriptJ.B A:=bondW _ _ _ (hs 0) (hs 2) (hs 3); have hh i: ScriptJ.B (X i):=stroll _ hq _; have hz j: ScriptJ.B (Y j):=stroll _ hy _
     have hv:T (q*y)=∑ i:Fin 3,∑ j:Fin 3,fair μ L A (X i*Y j):=by
          nth_rw 1 [show q=∑ i,X i from lumpSum q, show y=∑ i,Y i from lumpSum y]; simp_rw [Finset.sum_mul,Finset.mul_sum]; apply Eq.trans (fairSum μ L A hp' _ _ (fun i _=> teamB _ _ (fun j _=> height (hh i) (hz j)))); exact sum_congr rfl fun i _=> fairSum μ L A hp' _ _ fun j _=> height (hh i) (hz j)
     rw [show fair μ L (Stell p) (q*y)=_ from hv, bumper μ L p hp hs q hq,bumper μ L p hp hs y hy]; simp_rw [show ∀ i j,fair μ L A (X i*Y j)= _ from fun i j=> fairCox μ L p hp hs q y hq hy i j, Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum];simp
end YM.OPE.Libra.Shell
