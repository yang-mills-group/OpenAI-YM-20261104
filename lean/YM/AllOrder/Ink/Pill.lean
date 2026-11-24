import YM.AllOrder.Ink.Cast
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open Field
variable (A:Stalk α β) (H:Belt A a C) (u:Point α)(x:rule β n)(z:Site n)(ha:0≤a)(hc:0≤C)
include H ha hc
lemma stepped : (stepL A u).site n z x = (know A n x) (stood z u):= by
 let y(p:Point α):= stood z p; let w(j : Leaf n β)(v:Cover):= if j.1 = (y u).1 + wrap n v then A u.2 j.2 v else 0
 let f(k : (_i:β) × Cover):= (stepL A u).fee k * invoice z ((stepL A u).slip k) x; have hv : Summable f:= (knob A H u ha hc).total ha z x;
 have hh (j:Leaf n β):direct A n (y u) j * x j = ∑' v, w j v*x j:= ((regional H ha (y u) j).mul_right (x j)).tsum_eq.symm
 change (∑' v:(_i :β) ×Cover,f v) = ∑ i:Leaf n β,_; rw [hv.tsum_sigma,tsum_fintype,Fintype.sum_prod_type,sum_comm] -- comm which?
 change _= ∑ i:β,∑ j:Site n,direct A n (y u) (j,i)* x (j,i); apply Finset.sum_congr rfl; intro i _; simp_rw [hh]; rw [← Summable.tsum_finsetSum]; swap; · intro j _; exact ((regional H ha (y u) (j,i)).mul_right (x (j,i))).summable
 apply tsum_congr; intro v; unfold w; dsimp only; simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]; unfold f; simp only [stepL, invoice, paid, List.map_cons,List.map_nil,stood,map_add, List.prod_cons,List.prod_nil, mul_one, add_assoc,y]
-- pays replacing ONE factor with a linear plan. Meter no rate loss.
omit H ha hc
-- linear map may not be defined at α lacking Fintype; Good invariant if broadcast only. mask curves need variants later.

def promote (A:Stalk α β) : Slip (Point α) → Field β := fun s=> List.foldr (fun u v=> jointB (stepL A u) v) (plain 1 []) s

include H ha hc
lemma grocery (S:Slip (Point α)): (promote A S).Good a ((1+(Fintype.card β:ℝ)*C)^S.length* Real.exp (a*meter S)) S.length:= by
 let P':=1+(Fintype.card β:ℝ)*C
 induction S with
 | nil => simpa [meter,promote] using wordy (α:=β) (a:=a) 1 []
 | cons i S ih=>
   let t:= stepL A i; let B:= (Fintype.card β:ℝ)* (Real.exp (a*size i.1)*C); have hB:= knob A H i ha hc
   refine (mates t (promote A S) hB ih).debt le_rfl ?_ (by simp [add_comm]);
   let E:=Real.exp (a*size i.1); have he:B≤ P'*E:= by unfold P' B; rw [add_mul,one_mul,mul_left_comm ,mul_comm _ E]; exact le_add_of_nonneg_left (Real.exp_pos _).le
   change B*(P'^S.length*Real.exp _) ≤ P'^(S.length+1)*Real.exp (a*↑(size i.1+meter S)); rw [Nat.cast_add, mul_add, Real.exp_add]; apply (mul_le_mul_of_nonneg_right he (show 0≤ P'^S.length*Real.exp (a*meter S) by unfold P'; positivity)).trans_eq; unfold E; ring
lemma procure (S:Slip (Point α)) : (promote A S).site n z x=invoice z S (know A n x):= by induction S with
 | nil=> rw [promote,List.foldr_nil,plain_site,one_smul]; rfl -- reducible one?
 | cons i S ih=> change (jointB (stepL A i) (promote A S)).site n z x=_; rw [mate_site _ _ (knob A H i ha hc) (grocery A H ha hc S) ha,Pi.mul_apply,ih, stepped A H i x z ha hc]; rfl

variable (U:Field α)(h:U.Good a D k)
def confirm := Field.sum fun j:U.Ty=> Field.scale (promote A (U.slip j)) (U.fee j)
include h
local notation "Q"=>1+(Fintype.card β:ℝ)*C
local notation "S"=>fun j:U.Ty=> Field.scale (promote A (U.slip j)) (U.fee j)
local notation "V"=> fun j:U.Ty=>(1+(Fintype.card β:ℝ)*C)^k * U.price a j
lemma grip (j:U.Ty): ((S) j).Good a ((V) j) k:= by
   apply (Field.scale_good _ (grocery A H ha hc (U.slip j)) (U.fee j)).debt le_rfl _ (h.length j); let t:=Q; have ht:1≤t:= le_add_of_nonneg_right (mul_nonneg (by positivity) hc)
   change |U.fee j| *(t^_*_ ) ≤ t^k * _; unfold Field.price; rw [← mul_assoc (t^k),mul_comm (_*_)]; gcongr; exact h.length _
lemma well : (confirm A U).Good a ((1+(Fintype.card β:ℝ)*C)^k*D) k:= Field.keep S (grip A H ha hc U h) (budget_scale (show 0≤(Q)^k by positivity) h.pay)
lemma looks : (confirm A U).site n z x= U.site n z (know A n x):= by unfold confirm; rw [collection _ (grip A H ha hc U h) (budget_scale (show 0≤(Q)^k by positivity) h.pay) ha]; apply tsum_congr; intro i; rw [scale_site]; change U.fee i*_= _; rw [procure A H x z ha hc]
lemma run_total (n:Side): (confirm A U).table n=U.table n ∘ know A n:= by funext i; rw [Function.comp_apply,Field.table_apply,Field.table_apply]; exact Finset.sum_congr rfl (fun j _=>looks A H i j ha hc U h)
end Method
end YM.AllOrder.Ink
