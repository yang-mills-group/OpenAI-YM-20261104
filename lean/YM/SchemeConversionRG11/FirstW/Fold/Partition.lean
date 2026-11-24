import YM.SchemeConversionRG11.FirstW.Fold.Masts
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Lattice Pert Align Position Maxwell RawLabels MvPolynomial Warp SchemeConversionRG11
open scoped BigOperators Classical Topology
variable {G:Gauge}{F:Labels.Frames G}{n:Side}{r:ℕ} {T:Itinerary}
def Star3 (a:At G r 6): Finset (At G r 6):=apart G 6 a.1
def flowC (p:Players G r 6)(o:Full.Grid n r)(h:ℝ):= ∑ a:At G r 6,∑ b∈Star3 a,∑ c∈Star3 a,changeD o h p a b c
def flowV (p:Players G r 6)(o:Full.Grid n r)(h:ℝ):= ∑ a:At G r 6,∑ b∈Star3 a,∑ c ∈ Star3 a ∩ Star3 b,verbD o h p a b c
def morn (p:Players G r 6)(o:Full.Grid n r)(h:ℝ)(s:Fin r)(T:Sky G (Per n)):= ∑ a:Who G 6,∑ b:Who G 6,∑ i∈apart G 6 s,(3:ℂ) * (verbD o h p (s,a) (s,b) i - stagedV p o h (s,a) (s,b) i T)
private lemma cap_distrib {J K : Type*} [DecidableEq J][DecidableEq K] [Fintype J][Fintype K] (V C:J×K→J×K→J×K→ℂ)(ht:∀ a b c,V a b c=V b a c)(h : ∀ a b c,V a b c=V a c b)(he:∀ a b c,C a b c=C a c b):
 let A(i:J): Finset (J×K):=Finset.univ.filter fun x=> x.1≠i
 (∑ a,∑ b,∑ c,(V a b c+C a b c)) = (∑ a:J×K,∑ b∈A a.1,∑ c∈A a.1∩A b.1,V a b c)+(∑ a:J×K,∑ b∈A a.1,∑ c∈A a.1,C a b c) + ∑ j:J, ((∑ i:K,∑ s:K,∑ t:K, (V (j,i) (j,s) (j,t)+C (j,i) (j,s) (j,t)))+∑ i:K,∑ s:K,∑ c∈A j,(3*V (j,i) (j,s) c+2*C (j,i) (j,s) c)) := by
 intro A
 let I:= J×K; let B(j:J):Finset I:=Finset.univ.filter fun x=>x.1=j
 have hsplit(j:J)(F:I→ℂ):∑ i:I,F i=(∑ i∈A j,F i)+∑ i∈B j,F i:= Eq.symm (by simpa only [A,B,ne_eq,not_not] using Finset.sum_filter_add_sum_filter_not Finset.univ (fun i:I=> i.1≠ j) F)
 have hs(j:J)(F:I→ℂ): ∑ i∈B j,F i=∑ k:K,F (j,k):=by unfold B; rw [Finset.sum_filter, Fintype.sum_prod_type]; rw [Finset.sum_eq_single j]; simp; all_goals simp_all [Ne.symm]
 let R (a:I) (V:I→I→I→ℂ):= ∑ b∈A a.1,∑ c∈A a.1,V a b c
 let D(a:I)(V:I→I→I→ℂ):= ∑ b∈B a.1,∑ c∈B a.1,V a b c
 let E(a:I)(V:I→I→I→ℂ):= ∑ b∈B a.1,∑ c∈A a.1,V a b c
 have hp (V:I→I→I→ℂ)(hV:∀ a b c,V a b c=V a c b)(a:I): ∑ b:I,∑ c:I,V a b c=R a V+D a V+2*E a V:=by
   simp_rw [hsplit a.1 (V a _)]; rw [hsplit a.1 (fun i=>_)]; simp_rw [Finset.sum_add_distrib]
   have hp:∑ b∈A a.1,∑ c∈B a.1,V a b c=E a V:=by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> hV a _ _
   rw [hp,two_mul]; unfold R D E; abel
 -- residue E from both-equal-to-each-other
 let F(a:I):= ∑ b∈A a.1,∑ c∈A a.1∩A b.1,V a b c
 let Z (a b:I):= ∑ c∈B b.1,V a b c; let L(a:I):= ∑ b∈A a.1,Z a b
 have hq(a:I): R a V= F a+L a:=by
   unfold R L Z F; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro b hb; symm
   have ht:B b.1⊆ A a.1:=fun i hi=>by simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]; rw [(Finset.mem_filter.mp hi).2]; exact (Finset.mem_filter.mp hb).2
   rw [← Finset.sum_union,show A a.1 ∩ A b.1 ∪ B b.1=A a.1 from ?_]
   · ext i; simp only [Finset.mem_union,Finset.mem_inter]; by_cases he:i∈B b.1
     · simp [he,ht he]
     have hg : i∈A b.1:=by simp only [B,Finset.mem_filter,Finset.mem_univ,true_and] at he; simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,he, ne_eq,not_false_eq_true]
     simp [he,hg]
   apply Finset.disjoint_left.mpr; intro x hq m; have he: x∈ A b.1 :=(Finset.mem_inter.mp hq).2; exact ((Finset.mem_filter (p:=fun i:I=>i.1≠b.1)).mp he).2 ((Finset.mem_filter.mp m).2)
 have heq: ∑ i:I,L i=∑ i:I,E i V:=by
   unfold L; simp_rw [A,Finset.sum_filter]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; unfold E; rw [Finset.sum_comm]; simp_rw [A, Finset.sum_filter]; apply Finset.sum_congr rfl; intro b _; by_cases h' : b.1=a.1
   · simp [h']
   rw [if_pos (Ne.symm h'),if_pos h']; apply Finset.sum_congr rfl; intro z _; rw [ht b a z,h a b z]
 have whole(V:I→I→I→ℂ)(he:∀ a b c,V a b c=V a c b): ∑ a:I,∑ b:I,∑ c:I,V a b c = (∑ a:I,R a V)+(∑ a:I,D a V) +2*(∑ a:I,E a V) := by simp_rw [hp V he, Finset.sum_add_distrib, ← Finset.mul_sum] -- hp applies to whole sum first! matches triple by anchoring inner function
 have hsD (V:I→I→I→ℂ): (∑ a:I,D a V) = ∑ j:J,∑ i:K,∑ s:K,∑ t:K,V (j,i) (j,s) (j,t) := by
    have hh (a:I):D a V=∑ s:K,∑ t:K,V a (a.1,s) (a.1,t):=by unfold D; simp_rw [hs]
    change (∑ a:J×K,_) = _; rw [Fintype.sum_prod_type]; simp_rw [hh]
 have hsE (V:I→I→I→ℂ) : (∑ a:I,E a V) = ∑ j:J,∑ i:K,∑ s:K,∑ c∈A j,V (j,i) (j,s) c := by
    have hh(a:I): E a V=∑ s:K,∑ c∈A a.1,V a (a.1,s) c:=by unfold E; rw [hs]
    change (∑ a:J×K,_) = _; rw [Fintype.sum_prod_type];simp_rw [hh]
 simp_rw [Finset.sum_add_distrib,← Finset.mul_sum]; rw [whole V h,whole C he]; simp_rw [hq,Finset.sum_add_distrib, heq,hsD,hsE]; unfold F R; ring
lemma tilesD (p:Players G r 6) (o:Full.Grid n r)(h:ℝ) (R:Fin r→Sky G (Per n)) :
    ∑ a:At G r 6,∑ b:At G r 6,∑ c:At G r 6, (verbD o h p a b c+changeD o h p a b c)= flowV p o h+flowC p o h+∑ s:Fin r,(group3 p o h s+group2 p o h s (R s)+morn p o h s (R s)) := by
 let V:=verbD o h p; let C:=changeD o h p
 have ht (a b c:At G r 6): V a b c= V b a c:= by unfold V verbD; rw [dict_comm p b a]; congr 2; simp only [lap_shield,wheels,tower_sym (A:=arise h o a) (B:=arise h o b)]
 have he (a b c:At G r 6): V a b c= V a c b:=by unfold V verbD; rw [dict_comm _ c b]; congr 2; simp only [lap_shield,wheels,tower_cross (B:=arise h o b) (C:=arise h o c)]
 have hp (a b c:At G r 6): C a b c=C a c b:=by unfold C changeD; rw [dict_comm _ c b]; simp only [echoLeg,LinearMap.smul_apply]; rw [echoAt_symm] -- name?
 let f(s:Fin r):= group3 p o h s+∑ a:Who G 6,∑ b:Who G 6,∑ c∈apart G 6 s,(3*V (s,a) (s,b) c+2*C (s,a) (s,b) c)
 have H:∑ a:At G r 6,∑ b:At G r 6,∑ c:At G r 6,(V a b c+C a b c)=flowV p o h+flowC p o h+∑ s:Fin r,f s:=by
   have H:=cap_distrib V C ht he hp; dsimp only at H; unfold flowV flowC f group3; simp only [Star3,apart]; unfold V C at H ⊢; exact H
 unfold V C at H; rw [H]; apply congrArg (fun x:ℂ=> flowV p o h+flowC p o h +x); apply Finset.sum_congr rfl; intro i _; rw [add_assoc]; unfold f; apply congrArg (group3 p o h i + ·); unfold group2 morn; simp_rw [←Finset.sum_add_distrib]
 apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; unfold V C; ring
variable (F) (v:Fin r→E F 6)
def stock (n:Side)(o:Full.Grid n r)(h:ℝ)(v:Fin r→E F 6)(z:Buffer F 6): ℂ:= PowerSeries.coeff 1 (Full.row 6 F h o v) - ∑ i:Fin r,PowerSeries.constantCoeff (Full.row 6 F h o (update v i (z.val (v i))))
lemma stock_puck {T:Itinerary}{o:∀ i,Full.Grid (T.period i) r}{p:Points r}(d:Diorama T o p)(Q:Wash)(z:ℕ→Pack F)(hg:G.Simple): let W:= cloak F ∘ v
 Fleck T (fun i=>stock F (T.period i) (o i) (T.gap i) v (carryR (T.period i) (T.gap i) (z i))- (flowV W (o i) (T.gap i)+flowC W (o i) (T.gap i)+∑ s:Fin r,(costCT F Q T s o z (v s) W i+morn W (o i) (T.gap i) s (currents Q T o s i)))):=by
 intro W
 have ht {n:Side}(o:Full.Grid n r)(u:ℝ)(v:Fin r→E F 6): Full.row 6 F u o v= recipe 6 u o (uncap ∘ (cloak F ∘ v)) := by
   rw [recipe_at,Full.row_def]; apply congrArg _; exact _root_.funext (fun i=> (stretch F (v i)).symm)
 let Z i:= carryR (T.period i) (T.gap i) (z i)
 let uD i:= (∑ a:At G r 6, ∑ b:At G r 6, ∑ c:At G r 6,(verbD (o i) (T.gap i) W a b c+changeD (o i) (T.gap i) W a b c))
 have hh(i:ℕ)(s:Fin r): PowerSeries.constantCoeff (Full.row 6 F (T.gap i) (o i) (update v s ((Z i).val (v s))))=ZeroR (o i) (T.gap i) (update W s (cloak F ((Z i).val (v s)))) := by rw [ht]; unfold ZeroR; rw [show cloak F ∘ update v s ((Z i).val (v s))=update W s (cloak F ((Z i).val (v s))) from _root_.funext fun i=>by by_cases e:i=s <;> simp [W,e]] -- lemma name
 have h(i:ℕ): stock F (T.period i) (o i) (T.gap i) v (Z i)=renda (o i) (T.gap i) W- ∑ s:Fin r,ZeroR (o i) (T.gap i) (update W s (cloak F ((Z i).val (v s)))) := by unfold stock; simp_rw [hh,ht];rfl
 change Fleck T (fun i=>stock F _ _ _ v (Z i)-_); convert! straight_price (T:=T) (x:=o) (v:=p) d.hdiv d.ht d.hs hg W using 1; -- signatures
 ext1 i; rw [tilesD W (o i) (T.gap i) (fun s=>currents Q T o s i),h]; unfold costCT Z; simp_rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib]; abel
end YM.RG11.FirstW.Deck
