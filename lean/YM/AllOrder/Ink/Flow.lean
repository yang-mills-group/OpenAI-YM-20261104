import YM.AllOrder.Ink.Ripe
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open Field GaussianScore
variable {X:Field α} (H:X.Good a C k){F:Stalk α α}(h:Belt F a D)(ha:0≤a)(hD:0≤D)
-- translation exact norm error separately. derivative actual table. use boos.
include H h ha hD
lemma advance (n:Side) : flicker F n (X.table n) = (plan X (funds F)).table n+(plan X (trim F n)).table n:= by
 rw [Field.table,flicks F _ _ (fun i _=> (H.site ha i).2.1.read), table, table,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun z _=>?_ ; let A:= plan X (funds F); let B:= plan X (trim F n); ext1 v; let g(i : (j:X.Ty) × Held (X.slip j)):= A.fee i* invoice z (A.slip i) v; let r(i : (j:X.Ty) × Held (X.slip j)):= B.fee i* invoice z (B.slip i) v
 have hg:Summable g:= (crux F X H h ha hD).total ha z v; have hr:Summable r:= (critical F X H h ha hD n).total ha z v
 change flicker F n _ v=(∑' i,g i)+ ∑' i,r i; rw [← ((H.tests ha z (tool F v)).tsum_eq), ← Summable.tsum_add hg hr, (hg.add hr).tsum_sigma]; apply tsum_congr; intro y; let S:=X.slip y; let f (x : Held S):=senior S x; let g' (x:Held S):= secondary S x
 rw [flicker_seat, Finset.sum_apply, tsum_fintype,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; let u:= X.fee y; let v' := invoice z (child S i) v; let X':=funds F S i; let Y':=trim F n S i
 change u*(direct F n (stood z (f i)) (stood z (g' i))*v') = u*X'*v'+u*Y'*v'; rw [show direct F n (stood z (f i)) (stood z (g' i))=X'+Y' from (life (f i) (g' i) F z 0).trans (add_sub_cancel ..).symm]; ring
lemma carbon (n:Side) : let Y:=(plan X (funds F)); Prices (k-2) ((Fintype.card (Site n):ℝ)* ((k*k:ℕ)*((Real.exp (-a*n.val)*D)*C))) (flicker F n (X.table n)-Y.table n):= by intro Y; rw [advance H h ha hD]; simp only [show Y=plan X (funds F) from rfl, add_sub_cancel_left]; exact (critical F X H h ha hD n).binding ha
end Method
end YM.AllOrder.Ink
