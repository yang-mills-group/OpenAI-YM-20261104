import YM.OPE.Compatible.Cum.Egg
/-!
# finite decks and Boss operators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page
variable {I J E R:Type}{e d t u j:ℕ}{N:Side}
private def leftC (e d:ℕ)(i:Fin (d+1)): (Fin (e+(d+1)+1))≃ Fin (e+(d+1)+1):= Equiv.Perm.decomposeFin.symm (0,wand e d i)
private lemma left_comp (x:Fin (e+d+1)→R)(a:R)(i:Fin (d+1)):
     (Fin.cons a x:Fin (e+d+1+1)→R)∘ leftC e d i= Fin.cons a (x ∘ wand e d i):=by
        ext1 j; refine Fin.cases ?_ (fun u=> ?_) j <;> simp [leftC]
-- Braid wrappers. consume and orient
protected def Temper (e d:ℕ)(p:Script I (e+d+1)) : Script I (e+1+d):= Shell.slice (beginC e d) p
protected def Cycle (e d:ℕ)(p:Script I (e+(d+1)+1))(i:Fin (d+1)): Script I (e+d+1+1):= Shell.slice (leftC e d i) p
def knots (e d:ℕ)(p: Script I (e+(d+1)+1))(i:Fin (d+1))(A:Row I I): Script I (e+d):=Flume.Script.pad A (Shell.Cycle e d p i)
def orientY (u t:ℕ)(q:Script I (u+(t+1)))(i:Fin (t+1)):Script I (u+t+1):= slice (wand u t i) q
def mitt (e d u t:ℕ)(p: Script I (e+d+1))(q:Script I (u+(t+1)))(i:Fin (t+1))(A:Row I I): Script I (e+u+(d+t)):= slice (plank e d u t) (cotton A p (orientY u t q i))
variable [Fintype I] (a:Site N)
local notation "Q"=> deck I N
local notation "TK"=> Flume.Script.Tab I N
lemma scriptV (p:Script I t)(v:Fin t→ Q)(h: Summable p): orchestra p a v= scribe a p v:= (instruments p h a v).tsum_eq.symm
omit [Fintype I] in lemma tempered (x y:deck I N)(p: Script I (e+d+1)): scribe a (Shell.Temper e d p) (cue x y (e+1) d)=scribe a p (Fin.cons y (cue x y e d)):=by unfold Shell.Temper;rw [slice_pay,begin_pay]
omit [Fintype I] in lemma cyc_run (p : Script I (e+(d+1)+1))(x y z a':deck I N)(i:Fin (d+1)):
    scribe a p (Fin.cons a' (Function.update (cue x y e (d+1)) (pinT i) z))= scribe a (Shell.Cycle e d p i) (Fin.cons a' (Fin.cons z (cue x y e d))):=by
        unfold Shell.Cycle; rw [slice_pay, left_comp,cull]
section Law
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (L:Law E)(Z:E→L[ℝ] deck I N)
def Ferry (Z:E→L[ℝ] deck I N)(i:TK): Dual' E:= ((ContinuousLinearMap.proj i:deck I N→L[ℝ] ℝ) ∘L Z).toLinearMap
abbrev Oriel := mount L (Ferry Z)
-- expansion legs
omit [FiniteDimensional ℝ E] in
lemma beryl (x:E):Z x=∑ i:TK, Ferry Z i x • deltaH i:= by
    ext1 i;rw [Finset.sum_apply,sum_eq_single i]; · simp [deltaH,Ferry]
    · intro j _ h;simp [deltaH,Ne.symm h]
    simp
lemma sage (x:TK): Z (L.inverse (Ferry Z x))= ∑ i:TK, Oriel L Z x i • deltaH i:= beryl Z _
lemma tangles (p:Script I (e+(d+1)+1))(x y:Q)(z:E)(i:Fin (d+1))(h:Summable p):
    (∑ j:TK, φx x y Z ((orchestra p a).curryLeft (deltaH j)) (L.inverse (Ferry Z j)) i z)=routeTap (Oriel L Z) (Shell.Cycle e d p i) (cue (x+Z z) y e d) a:=by
       unfold routeTap; refine sum_congr rfl fun j _=>?_ ; let v:=cue (x+Z z) y e (d+1); let f:=((orchestra p a).curryLeft (deltaH j)); let K:= f.toContinuousLinearMap v (pinT i); change K (Z (L.inverse _))= _; rw [sage,map_sum]; apply sum_congr rfl;intro k _;rw [map_smul]; change _*(orchestra p a (Fin.cons _ _)) = _; apply congr_arg; rw [scriptV a p _ h,cyc_run]
lemma mittGo (p:Script I (e+d+1))(q:Script I (u+(t+1)))(V:Row I I)(hp:Summable p)(hq: Summable q)(hv:Whole V)(i:Fin (t+1))(x y:Q):
    scribe a (mitt e d u t p q i V) (cue x y (e+u) (d+t))=
    ∑ j:TK,∑ k:TK, V.acts N j k * scribe a p (Fin.cons (deltaH j) (cue x y e d))*library N q (Function.update (cue x y u (t+1)) (pinT i) (deltaH k)):=by
       unfold mitt; rw [slice_pay,plank_pay, readCotton hv hp]; swap
       · exact swing_sum q hq (wand u t i) -- names
       unfold drawP; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold library; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; unfold orientY; rw [slice_pay,cull]
end Law
end YM.OPE.Libra.Shell
