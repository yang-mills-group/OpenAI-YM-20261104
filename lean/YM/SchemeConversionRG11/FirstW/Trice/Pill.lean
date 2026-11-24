import YM.SchemeConversionRG11.FirstW.Trice.Comp
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {n:Side}
lemma tumble2 (o:Full.Grid n 3)(s:ℝ)(w:Players G 3 6)(i j k:P): spinC o s w i j k=spinC o s w i k j:= by unfold spinC; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun c _=> by simp only [changeD,echoLeg,LinearMap.smul_apply]; rw [echoAt_symm,dict_comm]
lemma decksC (o:Full.Grid n 3)(s:ℝ)(w:Players G 3 6) : flowC w o s= (∑ i:P, 2*spinC o s w i (foreL i) (aft i))+∑ i:P,(tracC o s i (foreL i) w+tracC o s i (aft i) w):=by
 let L:=spinC o s w; let f(i:P):=∑ j∈Finset.univ.erase i,∑ k∈Finset.univ.erase i,L i j k
 have h : flowC w o s=∑ i:P,f i:=by
    unfold flowC Star3 Deck.apart; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; dsimp only; simp_rw [feat]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; conv_lhs=> arg 2; intro a; rw [Finset.sum_comm]; -- now ∑ a,∑ k,∑ b,...
    rw [Finset.sum_comm];rfl
 rw [h,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold f; rw [flood_load i]; let a:=foreL i; let b:=aft i; simp_rw [Finset.sum_pair (Ne.symm (neg3 i))]
 change L i a a+ L i a b+(L i b a+L i b b)= 2*L i a b + (L i a a+ L i b b); rw [show L i b a=L i a b from tumble2 ..]; ring
variable (o:Full.Grid n 3) (s:ℝ)
def roam (g:P→Badge G)(o:Full.Grid n 3)(s:ℝ)(i:P):= Stele (g i) (glow i) (o i) s
def debtI (i j k:Who G 6):ℂ:= 6*(lapSky G n (arise s o (0,i)) (arise s o (1,j)) (arise s o (2,k)):ℂ) + 2*(((echoLeg s (o 0) i.val (arise s o (1,j)) (arise s o (2,k)):ℂ)+(echoLeg s (o 1) j.val (arise s o (2,k)) (arise s o (0,i)):ℂ))+(echoLeg s (o 2) k.val (arise s o (0,i)) (arise s o (1,j)):ℂ))
def debtG (g:P→Badge G):ℂ:= 6*(lapSky G n (roam g o s 0) (roam g o s 1) (roam g o s 2):ℂ) + ∑ i:P, (CardC (g i) (glow i) s (o i) (roam g o s (foreL i)) (roam g o s (aft i)):ℂ)
lemma loadV (g:P→Badge G)(i:P) : roam g o s i=∑ j:Who G 6,token (g i) (glow i) j • arise s o (i,j):= rfl
def copper (g:P→Badge G)(i j k:Who G 6):ℂ:= ct (g 0) true i * ct (g 1) false j*ct (g 2) false k
private lemma cash1 {E V:Type}[AddCommGroup E][Module ℝ E][Fintype V](x y z: V→ℝ)(p q r: V →E)(L:E→ₗ[ℝ] E→ₗ[ℝ] E→ₗ[ℝ] ℝ):
 (↑(L (∑ i:V,x i • p i) (∑ i:V,y i • q i) (∑ i:V,z i • r i)):ℂ)=∑ i:V,∑ j:V,∑ k:V,(x i:ℂ)*(y j:ℂ)*(z k:ℂ)* (L (p i) (q j) (r k):ℂ):= by
 simp only [map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,ofReal_mul,ofReal_sum,Finset.mul_sum]; -- lhs k,j,i
 conv_lhs=>rw [Finset.sum_comm]; arg 2; intro a; rw [Finset.sum_comm]
 rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>by ring
lemma sum_circle {X Y:Type}[Fintype X][AddCommMonoid Y](p:X→X→X→Y): ∑ i,∑ j,∑ k,p i j k=∑ j,∑ k,∑ i,p i j k:=by conv_lhs=>rw [Finset.sum_comm];arg 2; intro a; rw [Finset.sum_comm]; -- rfl
private lemma cash2 {E V:Type}[AddCommGroup E][Module ℝ E][Fintype V](x y z: V→ℝ)(p q: V → E)(L: V→ E→ₗ[ℝ] E→ₗ[ℝ] ℝ):
 (↑(2*∑ i:V,x i* L i (∑ i:V,y i • p i) (∑ i:V,z i • q i)):ℂ)=2*∑ i:V,∑ j:V,∑ k:V,(x i:ℂ)*(y j:ℂ)*(z k:ℂ)*(L i (p j) (q k):ℂ):= by
 simp only [ofReal_mul,ofReal_sum,ofReal_ofNat]; apply congrArg _; refine Finset.sum_congr rfl fun i _=> ?_; simp only [map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply, smul_eq_mul,ofReal_mul,ofReal_sum,Finset.mul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>by ring
lemma lap_proof (g:P→ Badge G): (lapSky G n (roam g o s 0) (roam g o s 1) (roam g o s 2):ℂ)= ∑ i:Who G 6,∑ j:Who G 6,∑ k:Who G 6,copper g i j k*(lapSky G n (arise s o (0,i)) (arise s o (1,j)) (arise s o (2,k)):ℂ):= by simp_rw [loadV]; exact cash1 _ _ _ (fun i=>arise s o (0,i)) (fun i=> arise s o (1,i)) _ _ -- may expensive
lemma spectral (g:P→Badge G)(i:P): (CardC (g i) (glow i) s (o i) (roam g o s (foreL i)) (roam g o s (aft i)):ℂ)=2* ∑ j:Who G 6,∑ k:Who G 6,∑ l:Who G 6,ct (g i) (glow i) j * ct (g (foreL i)) (glow (foreL i)) k*ct (g (aft i)) (glow (aft i)) l*(echoLeg s (o i) j.val (arise s o (foreL i,k)) (arise s o (aft i,l)):ℂ):= by
 simp_rw [loadV]; unfold CardC
 let L(a:Who G 6): FullT G n→ₗ[ℝ] FullT G n→ₗ[ℝ] ℝ:= echoLeg s (o i) a.val
 apply cash2 (token (g i) (glow i)) (token (g (foreL i)) (glow _)) (token (g (aft i)) (glow _)) (fun k=> arise s o (foreL i,k)) (fun k=> arise s o (aft i,k)) L
lemma totalG (g:P→Badge G): ∑ i:Who G 6,∑ j:Who G 6,∑ k:Who G 6,copper g i j k*debtI o s i j k = debtG o s g:= by
 rw [debtG,lap_proof]; simp_rw [spectral o s]
 -- reorder sums using cycle. explicit lemma C charges order
 let I:=Who G 6; let X(m:P)(i j k:Who G 6):ℂ:= ct (g m) (glow m) i * ct (g (foreL m)) (glow (foreL m)) j*ct (g (aft m)) (glow (aft m)) k*(echoLeg s (o m) i.val (arise s o (foreL m,j)) (arise s o (aft m,k)):ℂ)
 let P'(m:P):ℂ:= 2*∑ i:Who G 6,∑ j:Who G 6,∑ k:Who G 6,X m i j k; change _= 6*(∑ i:Who G 6,∑ j:Who G 6,∑ k:Who G 6,_) + ∑ i:P,P' i
 rw [show ∑ i:P,P' i=P' 0 + P' 1 + P' 2 from by simp [P, Fin.sum_univ_succ]; abel]; unfold P'; rw [← sum_circle (fun i j k=> X 1 j k i), sum_circle (X 2)]
 simp only [Finset.mul_sum,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl; intro j _;apply Finset.sum_congr rfl;intro k _
 unfold copper X debtI
 rw [show glow 0=true from by decide,show glow 1=false from by decide,show glow 2=false from by decide, show foreL 0=1 from by decide, show aft 0=2 from by decide, show foreL 1=2 from by decide,show aft 1=0 from by decide,show foreL 2=0 from by decide,show aft 2=1 from by decide]; rw [show glow 0=true from by decide,show glow 1=false from by decide,show glow 2=false from by decide]; ring
end YM.RG11.FirstW.Branch
