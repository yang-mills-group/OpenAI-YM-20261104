import YM.X.Charting.Gum
/-!
Stitch for later triangular CTs. Keeps costs quantities as defined (in particular engineering powers will multiply a polynomial period root asymptotic).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "K"=> (atTop:Filter ℕ)
variable {α β V:Type*}
variable (A:α→Beam q)(v:Beam q)(P:poly (α×Hair G))(hw:Away v (-v))(h:∀ i,Near v (A i))
section
variable [Finite α]
def sphere (o:α→Site n)(a:Bool):= shock (live a) (boil * (rename (stageAt o) P))
def fireline (o:α→Site n)(a:Bool) := ∑ i:PlaqAxes, ∑ j:Site n, fees o (live a) P (Stems.vertex i) j
lemma sphere_v (o:α→Site n)(a:Bool) : sphere P o a=(1/2:ℂ)*fireline P o a:= by
   unfold sphere boil fireline fees;rw [Fintype.sum_prod_type,Finset.sum_comm]; simp only [Finset.sum_mul, _root_.map_sum,smul_mul_assoc,map_smul, smul_eq_mul, one_div,Finset.mul_sum]
include hw hq h
lemma cost_correct : Vanished q (fun k=> let o i:= A i k; sphere P o true-fireline P o false) := by
   let X a:=fun k:ℕ=> ∑ p:PlaqAxes, foot A p P a k
   have H:Vanished q (X true -(2:ℂ) • X false):= by
       have he := Vanished.finSum (f:=fun p:PlaqAxes=> (foot A p P true) - (2:ℂ) • (foot A p P false)) (s:=Finset.univ) (q:=q) (fun p _=>by exact (dissent hq A v p P hw h))
       rw [show X true -(2:ℂ) • X false=∑ p:PlaqAxes,((foot A p P true)-(2:ℂ) • (foot A p P false)) from funext (fun i=>by simp [X, foot, ← Finset.sum_sub_distrib,Finset.mul_sum])]; exact he
   change Vanished q (fun k=> sphere _ (fun i=>A i k) true- _); simp_rw [sphere_v]; apply Eq.mp ?_ (supreme (1/2) H); congr 1; ext1 k; change (1/2:ℂ) * (X true k- 2*X false k)=(1/2:ℂ)* X true k-X false k;ring
end
variable [Fintype α][DecidableEq α] (S:α→Word G)
def prop0 := pot Finset.univ (fun i:α=> bookMark (S i) 0)
def prop1 := Jet.dot (fun i=>post i (bookMark (S i) 0)) (fun i=> post i (bookMark (S i) 1)) Finset.univ
variable (o:α→Site n)
lemma point_prop0 : road o S= rename (stageAt o) (prop0 S):= by unfold road prop0 pot; rw [_root_.map_prod]; apply Finset.prod_congr rfl; intro i _; rw [post,rename_rename]; rfl
lemma point_prop1 : triangle o S= rename (stageAt o) (prop1 S):= by unfold triangle prop1 Jet.dot; simp_rw [map_sum,map_mul,map_prod,transfers,hairAt,post, rename_rename];rfl

def purePoint :ℂ:= shock sale (rename (stageAt o) (prop0 S))
def plusPoint :ℂ:= shock sale (rename (stageAt o) (prop1 S)) - fireline (prop0 S) o false

omit [Fintype α] [DecidableEq α] in
lemma toll_cost (g: Word G): Charged q (fun k=> ((toll (epsilon q k) g:ℝ):ℂ)):= by
   have H (b:ℤ): Charged q (fun k=> ((ticket q b k:ℝ):ℂ)):= ⟨b,Ripe.eventual (B:=1) (Eventually.of_forall fun i=> (by simp [Complex.norm_real, Real.norm_of_nonneg (ticket_pos ..|>.le)]))⟩
   apply Eq.mp ?_ (Charged.mul (H (- (4:ℕ))) (H g.d)); congr 1; ext1 k; unfold toll; simp only [Pi.mul_apply,ticket_neg,ticket_nat,←Complex.ofReal_mul]; rw [eps_eq, inv_pow, inv_pow _ g.d]; congr 1; rw [div_eq_mul_inv,inv_inv]
omit [DecidableEq α] in
lemma ample : Charged q (fun k=> ((∏ i:α, toll (epsilon q k) (S i):ℝ):ℂ)):= by
   have hh (s : Finset α):Charged q (fun k=> ((∏ i∈s, toll (epsilon q k) (S i):ℝ):ℂ)):= by
      induction s using Finset.induction_on with
      | empty=> simpa only [Finset.prod_empty,Complex.ofReal_one] using! Charged.constant (q:=q) (1:ℂ)
      | insert i s hi ih=> simp_rw [Finset.prod_insert hi,Complex.ofReal_mul]; exact (toll_cost (S i)).mul ih
   exact hh _
include hw hq h
lemma cut_basis0 : Vanished q (fun k=> (rowP (fun i=> A i k) S (epsilon q k) 0:ℂ) - ((∏ i:α,toll (epsilon q k) (S i):ℝ):ℂ)*purePoint S (fun i=> A i k)):= by
   simp_rw [formula _ _ _ (side_even ..),purePoint, point_prop0,← mul_sub]; exact Vanished.right (ample S) (stepUV hq A v (prop0 S) hw h)
lemma cut_basis1 (hg:G.Simple) : Vanished q (fun k=> (rowP (fun i=> A i k) S (epsilon q k) 1:ℂ) - ((∏ i:α,toll (epsilon q k) (S i):ℝ):ℂ)*plusPoint S (fun i=> A i k)):= by
   let Q(k):α→Site (side q k):=fun i=>A i k; let B(k):= mean (rename (stageAt (Q k)) (prop1 S)); let W(k):=shock sale (rename (stageAt (Q k)) (prop1 S)); let y(k):=sphere (prop0 S) (Q k) true; let z(k):= fireline (prop0 S) (Q k) false
   let f:= (fun k=> Complex.ofReal (∏ i:α,toll (epsilon q k) (S i))); have hh : Vanished q (f*((B-W)-(y-z))):= Vanished.right (ample S) ((stepUV hq A v (prop1 S) hw h).sub (cost_correct hq A v (prop0 S) hw h)); intro i; refine (hh i).congr_left ?_; intro k; rw [formula' _ _ _ (side_even ..) hg,plusPoint,point_prop0,point_prop1,map_sub, mul_comm _ (boil)]; change f k*((B k-W k)-(y k-z k))=f k*(B k-y k)-f k*(W k-z k); ring
end YM.PositionX.Hinge
