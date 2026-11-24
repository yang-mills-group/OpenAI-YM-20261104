import YM.SchemeConversionRG11.FirstW.Trice.Worship
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Metric Set Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal Branch
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes}{n:Side}{R ρ:ℝ}
def view (p:Nodes)(x y z a b:Badge G):ℂ:= 3*tau x y z* (colC (![x,a,b])) * (impact (p 1) (p 2) (p 0) x.1 a.1 b.1 :ℂ)* pact p y a 1 * pact p z b 2
lemma literal_v (x y z a b:Badge G)(d:Diorama T u p)(hc:MarkGrid T c)(h:Box p R ρ): Tendsto (fun i=> literal (u i) (T.gap i) x y z a b) atTop (𝓝 (view p x y z a b+ view p x z y a b)) := by
 let g:P→Badge G:= ![x,a,b]; have ht:= heights d g h hc; have hp:= fortune d (day y z g)
 have he : amount p (day y z g)= pact p y a 1*pact p z b 2+pact p y b 2*pact p z a 1:=luxury d.ht ..
 rw [he] at hp; have H:=(ht.const_mul (3*tau x y z)).mul hp
 have hv : 3*tau x y z*(colC g*(impact (p 1) (p 2) (p 0) (g 0).1 (g 1).1 (g 2).1:ℂ))*(pact p y a 1*pact p z b 2+pact p y b 2*pact p z a 1)=view p x y z a b+view p x z y a b:= by unfold view;rw [tau_flip,show g 0=x from rfl,show g 1=a from rfl,show g 2=b from rfl]; unfold g; ring
 rw [hv] at H; exact H
lemma sum_value (p:Nodes) (G:Gauge) : (∑ x:Badge G,∑ y:Badge G,∑ z:Badge G,∑ a:Badge G,∑ b:Badge G,(view p x y z a b+view p x z y a b)) = (fullTransfer G p:ℂ) := by
 let U(x y z a b:Badge G):=2*view p x y z a b
 have he(x:Badge G): (∑ y:Badge G,∑ z:Badge G,∑ a: Badge G,∑ b:Badge G,(view p x y z a b+view p x z y a b))=∑ y:Badge G,∑ z:Badge G,∑ a:Badge G,∑ b:Badge G,U x y z a b:= by unfold U; rw [Finset.sum_comm]; simp_rw [Finset.sum_add_distrib,two_mul,Finset.sum_add_distrib]; rw [Finset.sum_comm (f:= fun y z=>∑ a:Badge G,∑ b:Badge G,view p x z y a b)]
 let C:=G.ColorIndex
 have hp (x y z:Badge G):∑ a:Badge G,∑ b:Badge G,U x y z a b=∑ i:P,∑ j:P,U x y z (i,y.2) (j,z.2):= by
    rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; simp_rw [Fintype.sum_prod_type]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_eq_single y.2]; rw [Finset.sum_eq_single z.2]; intro a _ ha; simp [U,view,pact,Ne.symm ha]
    · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [U,view,pact,Ne.symm ha]
    simp
 let V(i j k l m:P)(a b c:C):ℝ:= (6*colorF a b c ^ 2)*((eps3 i j k:ℝ)*mixed j l (p 0 - p 1)*mixed k m (p 0-p 2)*impact (p 1) (p 2) (p 0) i l m)
 have heq (i j k l m:P)(a b c:C): U (i,a) (j,b) (k,c) (l,b) (m,c)=↑(V i j k l m a b c):= by unfold U view pact colC V tau; simp; ring
 simp_rw [he,hp,Fintype.sum_prod_type]; -- A,B,C. reorder using direct finset.sum_comm
 conv_lhs=>
    arg 2; intro i
    rw [Finset.sum_comm]; arg 2; intro j
    arg 2; intro a; rw [Finset.sum_comm]; arg 2; intro k
    arg 2; intro b;rw [Finset.sum_comm]; arg 2; intro l;rw [Finset.sum_comm]
 conv_lhs=>
    arg 2;intro i;arg 2;intro j
    rw [Finset.sum_comm]; arg 2; intro k; arg 2; intro a
    rw [Finset.sum_comm];arg 2; intro l;rw [Finset.sum_comm]
 conv_lhs=>
    arg 2;intro i;arg 2; intro j;arg 2;intro k
    rw [Finset.sum_comm]; arg 2; intro l; rw [Finset.sum_comm]
 change (∑ i:P,∑ j:P,∑ k:P,∑ l:P,∑ m:P, ∑ a:C,∑ b:C,∑ c:C,U (i,a) (j,b) (k,c) (l,b) (m,c))=_
 simp_rw [heq,← ofReal_sum]; unfold V fullTransfer detector classified; simp_rw [Finset.mul_sum,Finset.sum_mul]; rfl
lemma financed (F:Labels.Frames G)(h:G.Simple)(d:Diorama T u p)(Z:ℕ→Pack F)(hp:Box p R ρ)(hc:MarkGrid T c)(hz:∀ W:Wash,stampB F Z T W): Tendsto (showP T F u (basic F) Z) atTop (𝓝 (fullTransfer G p:ℂ)) := by
 obtain ⟨R,hR,ht⟩:=diameter_q d.ht; let W:Wash:= ⟨R/3,R/2,by linarith,by linarith⟩; have he:= closed_fee F h d W (show W.rOut < R by change R/2<R; linarith) ht hc Z (hz W)
 let X:=SlateZ G; have hv: Tendsto (fun i=> litV (u i) (T.gap i) X) atTop (𝓝 (fullTransfer G p:ℂ)):= by
    unfold X; simp_rw [purchase,←sum_value p G]; refine tendsto_finsetSum _ fun _ _=> tendsto_finsetSum _ fun _ _=> tendsto_finsetSum _ fun _ _ => tendsto_finsetSum _ fun _ _=> tendsto_finsetSum _ fun _ _=> literal_v _ _ _ _ _ d hc hp
 have hf : Tendsto (fun i=>∑ j:P,(tracC (u i) (T.gap i) j (foreL j) X+tracC (u i) (T.gap i) j (aft j) X)) atTop (𝓝 0):= by
    apply tend_t; intro j _; simpa only [add_zero] using (vapor_trac F h d j _ (neg1 j).symm).add (vapor_trac F h d j _ (neg2 j).symm)
 have ht:=he.add (hv.add hf); rw [zero_add,add_zero] at ht; apply ht.congr; intro i; simp only [X,decksC,spinV_print,litV]; abel
end YM.RG11.FirstW
