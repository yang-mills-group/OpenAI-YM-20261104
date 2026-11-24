import YM.OPE.Compatible.Cum.Feed
/-!
# Query IPP for any multiplicative extras. Space tapes with locked slots
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter Set MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin LinearMap
variable {E F I J R:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
local notation "W"=> E→ℝ
variable (p:I→ℕ) [DecidableEq I](u:I→ℕ)(T:∀ i,Tensor.T F ℝ (u i+p i))
local notation "P"=> Finset I
variable {e d:ℕ}(f:Tensor.T F ℝ (e+d+1)) (x y:F)(Z:E→L[ℝ] F) [Fintype J] (a:J→ Dual' E)(B:J→F)
def story (p:I→ℕ)(u:I→ℕ)(T:∀ i,Tensor.T F ℝ (u i+p i))(x y:F)(Z:E→L[ℝ] F)(i:I):E→ℝ:= SX (d:=p i) x y Z (T i)
omit [DecidableEq I] [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] in
lemma branches (s:P): okP (story p u T x y Z) s:= fun i _=> cueBond x y Z (T i)
def FTl (e d:ℕ)(f:Tensor.T F ℝ (e+d+1))(x y z:F)(Z:E→L[ℝ] F): E→ℝ:= SX (d:=d) x y Z (f.curryLeft z)
omit [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] in
lemma FTc {j:F}: Bond (FTl e d f x y j Z):= cueBond x y Z (f.curryLeft j)
def Qyl (p:I→ℕ)(u:I→ℕ)(T:∀ i,Tensor.T F ℝ (u i+p i))(x y:F)(Z:E→L[ℝ] F)(i:I)(v:E): Fin (p i)→E→ℝ:=fun j=>φx x y Z (T i) v j
-- self add branch
private def Acne (d e:ℕ) (f:Tensor.T F ℝ (e+d+1))(k:F)(x y:F)(Z:E→L[ℝ] F)(v:E)(i: Fin d): E→ℝ:=φx x y Z (f.curryLeft k) v i
-- sum generic
omit [FiniteDimensional ℝ E][DecidableEq I][MeasurableSpace E][BorelSpace E] in
lemma Sumbond (s:P)(z:I→E→ℝ)(h: okP z s): Bond (∑ i∈s,z i):=by rw [show (∑ i∈s,z i)=fun x=>∑ i∈s,z i x from funext fun _=> Finset.sum_apply ..]; exact Bond.sum _ _ h
omit [FiniteDimensional ℝ E][DecidableEq I][MeasurableSpace E][BorelSpace E] in lemma Qbond (i:I)(v:E)(j:Fin (p i)): Bond (Qyl p u T x y Z i v j):= φBond ..
omit [Fintype J] in
private lemma rulesF (s:P)(w:E)(i:J):
   let p':=story p u T x y Z
   let v:=FTl e d f x y (B i) Z
   Tap μ L p' ((L.P w)*v) s = (∑ j,Tap μ L p' (Acne d e f (B i) x y Z w j) s) + ∑ k∈s,∑ j:Fin (p k), Tap μ L p' (v * Qyl p u T x y Z k w j) (s.erase k):=by
      intro Ti v
      let A(i):=∑ j:Fin (p i),Qyl p u T x y Z i w j; let t(j:Fin d):= Acne d e f (B i) x y Z w j
      have ht: ∀ i,Bond (t i):=fun i=> φBond ..; have hv(i j): Bond (Qyl p u T x y Z i w j):=Qbond ..; have hx:Bond v:= FTc ..; have H:= Query μ L Ti w v (∑ j,t j) A s (branches p u T x y Z s) (fun i _=>Sumbond _ _ fun j _=>hv i j) hx (Sumbond _ _ fun j _=> ht j) (awake x y Z _ w) (fun i _=> awake x y Z _ w)
      rw [H, prices _ _ _ _ (branches p u T x y Z _) _ _ (fun j _=>ht j)]; apply congr_arg; apply Finset.sum_congr rfl; intro k hk; unfold A; rw [Finset.sum_mul,prices μ L Ti (s.erase k) (branches p u T x y Z _) _ _ (fun j _=>(hv k j).mul hx)]; exact Finset.sum_congr rfl fun j _=>congr_arg (fun f:W=> Tap μ L Ti f (s.erase k)) (mul_comm ..)
-- pack sum branches
lemma storyF (s:P)(hp:∀ x:E,Z x=∑ i:J,a i x • B i):
   let p':=story p u T x y Z
   let N(i:J):= L.inverse (a i)
   Tap μ L p' (SX x y Z f (d:=d+1) (e:=e)) s= Tap μ L p' (FTl e d f x y x Z) s+
     (∑ j:Fin d,Tap μ L p' (∑ i:J,φx x y Z (f.curryLeft (B i)) (N i) j) s)+∑ k∈s,∑ j:Fin (p k),Tap μ L p' (∑ i:J,FTl e d f x y (B i) Z* Qyl p u T x y Z k (N i) j) (s.erase k):=by
       intro p' N; let V(i:J):= FTl e d f x y (B i) Z; let G(i:J):= (L.P (N i):W)*V i; let X(i:J)(j:Fin d):= φx x y Z (f.curryLeft (B i)) (N i) j; have hX(i:J)(j): Bond (X i j):= φBond x y Z _ _ _; let Y(k:I)(j:Fin (p k))(i:J):= V i*Qyl p u T x y Z k (N i) j; have hv:∀ j:J,Bond (V j):= fun i=>FTc ..; have hy(k j i):Bond (Y k j i):=(hv i).mul (Qbond ..); have hg(i:J): Bond (G i):= (Bond.glyph _).mul (hv i); let f₀:=FTl e d f x y x Z
       have he : SX (d:=d+1) (e:=e) x y Z f=f₀+∑ i:J,G i:=by
           funext v; unfold SX G; rw [cusp]; let u:=cue (x+Z v) y e d; change f.curryLeft (x+Z v) u=_; rw [map_add,_root_.add_apply]; apply congr_arg (fun r:ℝ=>f.curryLeft x u+r); calc
                 _= _:= congr_arg (fun t:F=> f.curryLeft t u) (hp v)
                 _= _:= by rw [map_sum,_root_.sum_apply, Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [map_smul, _root_.smul_apply,Pi.mul_apply,show L.P (N i)= _ from L.applies (a i)]; rfl -- names ambiguity
       rw [he, Tap_merge _ _ _ _ (branches p u T x y Z _) f₀ (∑ i,G i) (show Bond f₀ from FTc ..) (Sumbond _ _ fun i _=>hg i), prices _ _ _ _ (branches p u T x y Z _) _ _ (fun i _=> hg i)]; rw [add_assoc]; apply congr_arg; let a(i:J)(j:Fin d):=Tap μ L p' (X i j) s; have ht(i:J): Tap μ L p' (G i) s=(∑ j:Fin d,a i j)+∑ k∈s,∑ j, Tap μ L p' (Y k j i) (s.erase k):= rulesF μ L p u T f x y Z B s (N i) i -- infer
       change (∑ i,Tap μ L p' (G i) s)= _; simp_rw [ht]; rw [Finset.sum_add_distrib,Finset.sum_comm (f:=a)]; apply congr_arg₂
       · apply sum_congr rfl;intro j _; exact (prices _ _ _ _ (branches p u T x y Z _) _ _ fun i _=>hX i j).symm
       rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl;intro j _; exact (prices _ _ _ _ (branches p u T x y Z _) _ _ fun i _=>hy k j i).symm
end YM.OPE.Libra.Shell
