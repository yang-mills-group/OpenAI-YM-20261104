import YM.SchemeConversionRG11.FirstW.Trice.Pill
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {n:Side}{R ρ:ℝ}
lemma transportG (x:Full.Grid n 3)(v:Site n)(t:ℝ)(g:P→Badge G): debtG (fun i=>x i-v) t g=debtG x t g:= by
 have he(i:P): roam g (fun i=> x i-v) t i=tracing v (roam g x t i):= by unfold roam Stele; simp only [map_sum,map_smul,river,consumes]
 unfold debtG; simp only [he,turnV,CardC,echoLeg,LinearMap.smul_apply,echo_translate,sub_add_cancel]
def column_s (T:Itinerary)(p:∀ i,Full.Grid (T.period i) 3)(g:P→Badge G)(i:ℕ):= debtG (p i) (T.gap i) g
lemma heights (d:Diorama T u p)(g:P→Badge G)(h:Box p R ρ)(hc:MarkGrid T c): Tendsto (column_s T u g) atTop (𝓝 (colC g* (impact (p 1) (p 2) (p 0) (g 0).1 (g 1).1 (g 2).1:ℂ))) := by
 let s (i:P)(k:ℕ): Site (T.period k):=u k i - Full.center (T.period k); have hs(j:P): sails T (s j) (p j):= d.hs j
 have he:= sieve (x:=p) T c g s h hs hc; let w(i:P):=(g i).1
 have ht:= he.add (tendsto_finsetSum Finset.univ (fun i _=> earned g i hs d.ht))
 rw [show -(colC g*∑ j:P,pass w p R ρ j mainPair 0)+(∑ i:P,colC g*atMarkQ w p i 0)= colC g*(impact (p 1) (p 2) (p 0) (g 0).1 (g 1).1 (g 2).1:ℂ) from ?_] at ht; rotate_left
 · rw [← show paths w p R ρ 0= _ from gets h w]; unfold Triad.paths; rw [Finset.sum_sub_distrib,mul_sub,←Finset.mul_sum]; abel
 apply ht.congr; intro i; let o: Full.Grid (T.period i) 3:= u i; let k:=Full.center (T.period i); let x(j:P):=o j-k
 rw [column_s,← transportG (u i) k]; unfold debtG; congr 1
 · have hp(j:P): nativeM T (firstK g T s j) i= roam g x (T.gap i) j:= by unfold firstK nativeM Laurel;rw [smul_inv_smul₀ (T.positive i).ne']; rfl
   unfold tagV; rw [hp,hp,hp];push_cast;rfl -- progress?
-- sum assembly algebra in bases
variable (o:Full.Grid n 3)(s:ℝ)(Q:Players G 3 6)
def litV (o:Full.Grid n 3)(s:ℝ)(v:Players G 3 6):=6*slitW o s v 0 1 2+∑ i:P, 2*spinC o s v i (foreL i) (aft i)
def loot1 (i j k:Who G 6) := dict (2,k) (dict (1,j) (dict (0,i) Q))
lemma lit_here (o:Full.Grid n 3)(s:ℝ)(P':Players G 3 6): litV o s P'= ∑ i:Who G 6,∑ j:Who G 6,∑ k:Who G 6,debtI o s i j k*ZeroR o s (loot1 P' i j k) := by
 let p(i:P):=2*spinC o s P' i (foreL i) (aft i)
 unfold litV; rw [show ∑ i:P,p i=p 0+p 1+p 2 from by simp [P,Fin.sum_univ_succ];abel]
 change 6*slitW o s P' 0 1 2+(2*spinC o s P' 0 1 2+2*spinC o s P' 1 2 0+2*spinC o s P' 2 0 1)=_
 unfold slitW spinC; rw [← sum_circle (fun i j k:Who G 6=> changeD o s P' (1,j) (2,k) (0,i)), sum_circle (fun i j k:Who G 6=>changeD o s P' (2,i) (0,j) (1,k))]; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _
 unfold verbD changeD loot1 debtI
 let a:At G 3 6:=(0,i); let b:At G 3 6:=(1,j); let c:At G 3 6:=(2,k)
 rw [dict_comm (dict b P') a c,dict_comm P' a b,dict_comm P' a c,dict_comm (dict a P') b c] -- orientation fix
 dsimp only; ring
lemma pillars (j k l:Who G 6): loot1 (SlateZ G) j k l=![D1 j (orbZ G),D1 k (seaU G),D1 l (seaU G)]:= by unfold loot1; rw [at0 _,at1 _,at2 _];rfl
abbrev day (b c:Badge G)(g:P→Badge G): Players G 3 6 := ![β b * β c,θ (g 1),θ (g 2)]
private lemma S35 {A B:Type*}[Fintype A][Fintype B](f:A→A→A→B→B→B→B→B→ ℂ): (∑ a,∑ b,∑ c,∑ u,∑ v,∑ w,∑ i,∑ j,f a b c u v w i j)= ∑ u,∑ v,∑ w,∑ i,∑ j,∑ a,∑ b,∑ c,f a b c u v w i j := by simpa only [Fintype.sum_prod_type] using! Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun p:A×A×A=> fun q:B×B×B×B×B=> f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
def literal (t w b c e:Badge G) := (3*tau t w b)*(debtG o (s) (![t,c,e]))*ZeroR o s (day w b (![t,c,e])) -- shadow
lemma get_ink (x y z: Badge G): (![x,y,z]:P→Badge G) 2=z:=rfl
lemma purchase (o:Full.Grid n 3)(s:ℝ): litV o s (SlateZ G)= ∑ x:Badge G,∑ y:Badge G,∑ z:Badge G,∑ u:Badge G,∑ v:Badge G, literal o s x y z u v:= by
 obtain ⟨M,h⟩:= tall_eq (G:=G) o s; obtain ⟨L,H⟩:= stamps M
 let g(x y z u v:Badge G):= (3*tau x y z)*ZeroR o s (day y z (![x,u,v])); let f(a b c:Who G 6)(x y z u v:Badge G):= copper (![x,u,v]) a b c *debtI o s a b c * g x y z u v
 have he(a b c:Who G 6) : debtI o s a b c * ZeroR o s (loot1 (SlateZ G) a b c)=∑ x:Badge G,∑ y:Badge G,∑ z:Badge G,∑ u:Badge G,∑ v:Badge G,f a b c x y z u v:= by
   rw [pillars,← h,←H,orb_one, sea_one, sea_one]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]; simp_rw [Finset.mul_sum]
   -- order likely v,u,x,y,z
   conv_lhs=>
       rw [Finset.sum_comm]
       arg 2; intro u; rw [Finset.sum_comm]
       arg 2; intro x; rw [Finset.sum_comm]
       arg 2; intro y; rw [Finset.sum_comm]
   conv_lhs=>
       rw [Finset.sum_comm];arg 2; intro x; rw [Finset.sum_comm]
       arg 2; intro y; rw [Finset.sum_comm]
   exact Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=> Finset.sum_congr rfl fun z _=>Finset.sum_congr rfl fun u _=>Finset.sum_congr rfl fun v _=> by rw [H,h]; simp only [f,g,day,copper, Matrix.cons_val_zero, show ( ![x,u,v]:P→Badge G) 1=u from rfl,get_ink]; unfold β θ; ring
 rw [lit_here]; simp_rw [he,S35 f]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=> Finset.sum_congr rfl fun z _=> Finset.sum_congr rfl fun u _=>Finset.sum_congr rfl fun v _=>?_
 simp_rw [f,←Finset.sum_mul,totalG]; unfold g literal; ring
end YM.RG11.FirstW.Branch
