import YM.FormalOPE.RG10.StationaryMarks.Lower
/-!
 # Coupling schedule formal and variable weights

 Schurs & stationary series always power series only at each finite regulator, sums finite.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
abbrev Tracks (f:ℝ→ℝ)(F:PowerSeries ℝ) := Aspiration f (Tested.term F)
namespace Tracks
variable {a b:ℝ→ℝ} {A B:PowerSeries ℝ}
@[simp] lemma asTerm (f:ℕ→ℝ): term (PowerSeries.mk f)=f:= funext fun _=> PowerSeries.coeff_mk ..
@[simp] lemma asSeries (F:PowerSeries ℝ): PowerSeries.mk (term F)=F:= PowerSeries.ext fun _=> coeff_mk ..
lemma add (h:Tracks a A)(g:Tracks b B): Tracks (a+b) (A+B):= by
 unfold Tracks; rw [show term (A+B) = term A + term B from funext (fun i=> map_add (coeff (R:=ℝ) i) A B)]; exact Aspiration.add h g
lemma mul (h:Tracks a A)(g:Tracks b B): Tracks (a*b) (A*B):= by
 have hi:= Aspiration.prod h g; rw [conv, asSeries,asSeries] at hi; exact hi
lemma sum {I:Type}(s:Finset I)(u:I→ℝ→ℝ)(v:I→PowerSeries ℝ)(h:∀ i∈s,Tracks (u i) (v i)): Tracks (∑ i∈s,u i) (∑ i ∈s,v i):= by
 unfold Tracks; rw [show term (∑ i∈s,v i)=∑ i∈s,term (v i) from funext (fun i=> by simp [term,Finset.sum_apply])]; exact Aspiration.sum s u (fun i=>term (v i)) h
lemma const (x:ℝ): Tracks (fun _=>x) (C x):= by
 unfold Tracks; convert Aspiration.single x 0 using 1 <;> try rfl
 · funext; simp
 funext k; simp [term,coeff_C]
lemma prod {I:Type}(s:Finset I)(u:I→ℝ→ℝ)(v:I→PowerSeries ℝ)(h:∀ i∈s,Tracks (u i) (v i)):Tracks (∏ i∈s,u i) (∏ i∈s,v i):= by
 induction s using Finset.induction with
 | empty => simp only [Finset.prod_empty]; simpa using! const 1
 | insert i s hi hs=> rw [Finset.prod_insert hi,Finset.prod_insert hi]; exact Tracks.mul (h i (by simp)) (hs (fun j hj=> h j (by simp [hj])))
lemma neg (h:Tracks a A):Tracks (-a) (-A):= by
 simpa only [map_neg,map_one,neg_mul,one_mul,(show (fun _=> -(1:ℝ))=- (1:ℝ→ℝ) from rfl)] using (Tracks.mul (const (-1)) h)
lemma sub (h:Tracks a A)(g:Tracks b B):Tracks (a-b) (A-B):= by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add g.neg

-- real schedule f(g) used *as is*. division by common powers doesn't lose final order:
-- choose next order internally with Aspiration.shift after verifying vanishing of a coefficient.
 def deduct (A:PowerSeries ℝ)(p:ℕ): PowerSeries ℝ:= PowerSeries.mk fun i=>term A (p+i)
lemma clipped (ha:Tracks a A)(w:ℕ)(h:∀ i<w,term A i=0):Tracks (fun t=> (t⁻¹)^w * a t) (deduct A w) := by unfold deduct Tracks; rw [asTerm]; exact (Aspiration.shift ha h)
 def rate (a:ℝ→ℝ)(A: PowerSeries ℝ): ℝ→ℝ:= fun t=> (term A 0 - a t)/t
 def shadow (A: PowerSeries ℝ): PowerSeries ℝ:= - deduct A 1
lemma start (h:Tracks a A):Tracks (rate a A) (shadow A):= by
 have ha:= Tracks.clipped (Tracks.sub h (const (term A 0))) 1 (by
   intro i hi; obtain rfl:i=0:= Nat.lt_one_iff.mp hi; unfold term; simp)
 convert Tracks.neg ha using 1
 · funext t; simp [rate, div_eq_mul_inv]; ring
 rw [shadow]; congr 1; ext k; simp [deduct,term,coeff_C]
end Tracks
end YM.FormalOPE.RG10.StationaryMarks
