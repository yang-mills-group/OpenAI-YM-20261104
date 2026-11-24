import YM.OPE.Compatible.Words.York
/-!
# Gaussian ODE
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {I J:Type}[Fintype I]{n k m d:ℕ}
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
variable (x:PAD I)(Z:E→L[ℝ] PAD I)(t:ℝ)
local notation "P!"=> PAD I
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma rays (p:Pole P! (n+1)) (h: Tensor.Sym p)(i:E): deriv (fun k:ℝ=> oval Z x k p i) t= (((n+1:ℕ):ℝ)*oval Z x t (p.curryLeft (Z i)) i):= (rayP x (Z i) t p h).deriv -- u unused
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma alongP (a:E)(p:Pole P! (n+1)) (h:Tensor.Sym p)(i:E)(k:ℝ): HasDerivAt (fun r:ℝ=> oval Z x t p (a+r•i))
    ((((n+1:ℕ):ℝ)*t)*oval Z x t (p.curryLeft (Z i)) (a+k • i)) k:=by
      have hp:=rayP (n:=n) (x+t • Z a) (t • Z i) k p h; have ht(r:ℝ): x+t • Z (a+r • i)= x+t• Z a+r • (t • Z i):=by rw [map_add,map_smul,smul_add,smul_comm t r,add_assoc]
      unfold oval; simp_rw [ht]; convert! hp using 1; rw [map_smul]; unfold Tensor.diagonal; rw [_root_.smul_apply]; change _=((n+1:ℕ):ℝ)*(t*_);ring
lemma broadcast (a:I)(p:Pole P! (n+2))(h:Tensor.Sym p):
      A.average μ (⇑(coQ Z a)* (oval Z x t (p.curryLeft (Pi.single a 1))))=
      (↑(n+1:ℕ)*t)* A.average μ (oval Z x t ((p.curryLeft (Pi.single a 1)).curryLeft (Z (A.inverse (coQ Z a))))):=by
        let q:= p.curryLeft (Pi.single a 1); let v:=A.inverse (coQ Z a); let D:= q.curryLeft (Z v); let c:ℝ:=↑(n+1:ℕ)*t; rw [show coQ Z a=A.P v from (A.applies _).symm] -- rhs may rewrite v
        change A.average μ (⇑(A.P v)*oval Z x t q)=c*A.average μ (oval Z x t (q.curryLeft (Z (A.inverse (A.P v)))))
        rw [Law.solves,← scooted]; refine bask μ A v (oval Z x t q) (c • oval Z x t D) (levied ..) (Bond.scale c (levied ..)) ?_; intro i u; exact alongP _ _ _ _ _ (Coin.hark2 p _ h) v u
abbrev balls (n:ℕ):ℝ:= ↑n
lemma brewC {k:ℕ}(q:Pole P! (k+1))(y:P!): q.curryLeft y= ∑ i:I,y i • q.curryLeft (Pi.single i 1):=by
     exact (congr_arg (q.curryLeft) (show y= ∑ i:I,y i • Pi.single i 1 by funext j; simp [Finset.sum_apply, Pi.single_apply])).trans (by simp)
omit [MeasurableSpace E] [BorelSpace E][FiniteDimensional ℝ E] in lemma ovalSm (p:Pole P! n)(c:ℝ): oval Z x t (c • p)= c • oval Z x t p:=rfl
lemma aroma (p:Pole P! (n+2))(h:Tensor.Sym p): HasDerivAt (fun u:ℝ=>A.average μ (oval Z x u p)) (t*A.average μ (oval Z x t (wind n • Semester (chamber A Z) p))) t:=by
       let q(i:I):= p.curryLeft (Pi.single i 1); let Q(i:I):= oval Z x t (q i); let s' (i:I):= coQ Z i; let S:= chamber A Z; let f(t:ℝ×E):= oval Z x t.1 p t.2; let R(i:I):= (p.curryLeft (Pi.single i 1)).curryLeft (Z (A.inverse (coQ Z i))); have ht : A.average μ (oval Z x t (Semester S p))=∑ i,A.average μ (oval Z x t (R i)):=by
            let V:=∑ i:I,oval Z x t (R i); have he :oval Z x t (Semester S p)= V:=by
                 funext y; let r:=x+t • Z y; unfold V; rw [Finset.sum_apply]; change Semester S p (fun _=>r)= ∑ i:I, R i (fun _=>r); rw [stanzaR]; refine sum_congr rfl ?_; intro i _; unfold R; rw [brewC (q:=p.curryLeft (Pi.single i 1)) (Z (A.inverse (coQ Z i))),_root_.sum_apply];rfl -- likely not
            rw [he, science μ A _ _ fun _ _=> levied ..]
       let l:= (balls (n+1))*t; let u:ℝ:= balls (n+2); have hx : (fun y:E=>deriv (fun i:ℝ=> f (i,y)) t)= u • ∑ i:I,(⇑(s' i)) *(Q i):=by
            funext i; rw [show deriv _ _= u*oval Z x t (p.curryLeft (Z i)) i from rays x Z t p h i, Pi.smul_apply,Finset.sum_apply,brewC p]; change u* (Tensor.diagonal _ _) = u * _; congr 1; unfold Tensor.diagonal;rw [_root_.sum_apply]; rfl --
       have hp:= hotrod μ A f (ovalQ Z x p) t; convert! hp using 1; rw [hx,scooted,science μ A univ _ (fun i _=> (Bond.glyph (s' i)).mul (levied ..)), ovalSm, scooted, ht]
       simp_rw [show ∀ i:I,A.average μ (⇑(s' i)*oval Z x t (q i))= l* A.average μ (oval Z x t (R i)) from fun i=> broadcast μ A x Z t i p h]; rw [← mul_sum]; change t*(((n+2:ℕ)*(n+1:ℕ):ℝ)*_)= _; unfold l u balls; push_cast;ring
end YM.OPE.Silt
