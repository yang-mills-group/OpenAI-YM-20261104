import YM.OPE.Compatible.Swoon.Sod
/-!
# Gaussian ledger in arbitrary basis. no invertibility in an accessor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Flock
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Matrix
variable {E F I:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
section matrix
variable [Fintype I]
def mount (p:I→Dual' E):Matrix I I ℝ:= Matrix.of fun i j=> L.wick (p i) (p j)
def ripple (p:I→Dual' E)(Q:Matrix I I ℝ):E→ℝ:= ∑ i:I,∑ j:I,Q i j • (⇑(p i)*⇑(p j))
omit [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] in
private lemma rider (q:I→E→ℝ)(h:∀ i,Bond (q i)): Bond (∑ i:I,q i):= by rw [show (∑ i:I,q i)= fun x:E=>∑ i,q i x from funext fun i=> sum_apply i ..]; exact Bond.sum _ _ fun i _=>h _
omit [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] in
lemma ripple_h (p:I→Dual' E)(Q:Matrix I I ℝ): Bond (ripple p Q):= rider _ fun i=> rider _ fun j=> Bond.scale _ ((Bond.glyph (p i)).mul (Bond.glyph (p j)))
lemma paddle (p:I→Dual' E)(Q:Matrix I I ℝ): L.average μ (ripple p Q)=(Q*mount L p).trace:=by
     let V:=mount L p; unfold ripple; rw [science]; refine sum_congr rfl fun i _=>?_; rw [science]; change _ = ∑ j:I,Q i j*V j i; refine sum_congr rfl fun j _=>?_; rw [scooted,summer,wix_sym μ L]; rfl; exact fun j _=> Bond.scale _ ((Bond.glyph _).mul (Bond.glyph _)); exact fun i _=>rider _ fun j=> Bond.scale _ ((Bond.glyph _).mul (Bond.glyph _)) -- goals scopes wrong
lemma swimmer (p:I→Dual' E)(A B:Matrix I I ℝ)(h:B.transpose=B):
    let V:=mount L p
    L.average μ (ripple p A*ripple p B)=L.average μ (ripple p A)*L.average μ (ripple p B)+2*(A*V*B*V).trace:=by
      intro V; let Q(i j:I):= ⇑(p i)*⇑(p j); have hQ i j:Bond (Q i j):=(Bond.glyph (p i)).mul (Bond.glyph (p j)); have ht:=ripple_h p B; have hv : ∀ i j,V i j=V j i:= fun i j=>wix_sym μ L (p i) (p j); let w(i j:I):= V i j*L.average μ (ripple p B)+2*(V*(B*V)) j i
      have hw(i j):L.average μ (Q i j*ripple p B)=w i j:=by
           have hy := paddle μ L p B; unfold w; rw [hy]; change _= V i j* (B*V).trace+ _; let T:= B*V
           have hh(x y): L.average μ (Q i j*Q x y)=V i j*V x y+V i x*V j y+V i y*V j x:=by
                change L.average μ ((⇑(p i)*⇑(p j))*(⇑(p x)*⇑(p y)))=_; rw [← mul_assoc]; exact squareQ μ L ..
           have hl:L.average μ (Q i j*ripple p B)=∑ k:I,∑ x:I,B k x*(V i j*V x k+V i k*V j x+V i x*V j k):=by
                unfold ripple; simp_rw [Finset.mul_sum]; rw [science]; refine sum_congr rfl fun k _=>?_; rw [science]; refine sum_congr rfl fun x _=>?_; rw [mul_smul_comm,scooted, hh,hv k x] ; exact fun x _=> (hQ i j).mul (Bond.scale _ (hQ _ _)); exact fun k _=> rider _ fun x=> (hQ i j).mul (Bond.scale _ (hQ _ _))
           rw [hl]; let f(k x:I):=B k x*(V i k*V j x); let g(k x:I):=B k x*(V i x*V j k)
           change _= V i j*(T.trace)+2*(V*T) j i; rw [show (∑ k:I,∑ x:I,B k x*(V i j * V x k+V i k*V j x+V i x*V j k))=∑ k:I,∑ x:I,(V i j*(B k x*V x k)+ g x k +g k x) from ?_]; simp_rw [Finset.sum_add_distrib,← Finset.mul_sum]; simp only [show ∀ k, (∑ x:I,B k x*V x k)= T k k from fun _=>rfl]
           rw [sum_comm (f:=fun k x=>g x k), show (∑ k:I,∑ x:I,g k x)=(V*T) j i from ?_]; change V i j*T.trace+_+_= _;ring
           · simp_rw [T, Matrix.mul_apply, mul_sum]; apply sum_congr rfl fun k _=>sum_congr rfl fun x _=>?_ ; unfold g; rw [hv i x]; ring
           refine sum_congr rfl fun k _=> sum_congr rfl fun x _=>?_ ; unfold g; rw [show B x k=B k x from congr_fun (congr_fun h k) x]; ring
      let a (i j:I):= A i j; let q:=ripple p B
      have hk : L.average μ (ripple p A*q)=∑ i:I,∑ j:I,A i j*w i j:=by
         unfold ripple; simp_rw [Finset.sum_mul]; rw [science]; refine sum_congr rfl fun i _=> ?_; rw [science]; refine sum_congr rfl fun j _=>?_; rw [smul_mul_assoc,scooted, hw]; exact fun j _=> (Bond.scale _ (hQ _ _)).mul ht; exact fun i _=>rider _ (fun j=>(Bond.scale _ (hQ _ _)).mul ht)
      change L.average μ (ripple p A*q)= L.average μ _* L.average μ q+_; rw [hk,paddle,show A*V*B*V=A*(V*(B*V)) by simp [Matrix.mul_assoc]]
      simp_rw [w, mul_add, sum_add_distrib]; apply congr_arg₂
      · change _=(∑ i:I,(∑ j:I,A i j*V j i))*_; rw [Finset.sum_mul]; refine sum_congr rfl fun i _=>?_ ; rw [Finset.sum_mul]; exact sum_congr rfl fun j _=>by rw [hv i j, mul_assoc]
      change _= 2*∑ i:I,∑ j:I,A i j*(V*(B*V)) j i; simp_rw [mul_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; ring
end matrix
end YM.OPE.Libra.Flock
