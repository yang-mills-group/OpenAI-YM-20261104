import YM.WilsonCoeffUV.Root.Post.MatrixPack
/-!
# Finite cast without torsion and on thermodynamic cover.
The analytic read m from C.F textual. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}

abbrev Thesis (F:Frame G h) D:= BookC F (Vote D) (YForest G)

def Standby (v: ChamberTen G (Vote D) r): Prop:=∃ s A:ℝ, 0<s∧Twig 0 s A v
lemma Standby.zero : Standby (0:ChamberTen G (Vote D) r):= ⟨1,0,one_pos,Cork.zero⟩
lemma Standby.mix {P Q:ChamberTen G (Vote D) r}(p:Standby P)(q:Standby Q): Standby (P+Q):=by
    obtain ⟨s,a,hp,h⟩:=p; obtain ⟨t,b,ht,h'⟩:=q; exact ⟨min s t,_,lt_min hp ht,Cork.add (Cork.mono h (min_le_left ..)) (Cork.mono h' (min_le_right ..))⟩
lemma Standby.μ {P:ChamberTen G (Vote D) r}(p:Standby P)(b:ℝ): Standby (b•P):=by obtain ⟨s,a,hp,h⟩:=p; exact ⟨s,_,hp,Cork.μ h b⟩
lemma Standby.sum {S:Finset E}{P:E→ChamberTen G (Vote D) r}(p:∀ i∈ S,Standby (P i)):Standby (∑ i∈S,P i):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Standby.zero
    | insert a b e ih=> rw [Finset.sum_insert e]; exact (p a (Finset.mem_insert_self ..)).mix (ih fun i hi=>p i (Finset.mem_insert_of_mem hi))
lemma Standby.affixed {Y:Single G D}(hp:∀ i r,Standby (Y i r))(A: Blue.Cost) (e r:ℕ): Standby (affix A Y e r):= by unfold affix; rw [Finset.sum_apply]; exact Standby.sum fun _ _=> (hp ..).μ _
lemma echo_sum (F:Frame G h)(i:Alma F){P:E→ ChamberTen G (Vote D) r}(S:Finset E)(h:∀ j∈S,Standby (P j)): echoS F (∑ v∈S,P v) i=∑ v∈S,echoS F (P v) i:=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact echo_zero F D r i
    | insert a b e ih=>
       have hg:∀ j∈ b,Standby (P j):=fun j hj=> h j (Finset.mem_insert_of_mem hj); obtain ⟨s,B,hs,p⟩:= h a (Finset.mem_insert_self ..); obtain ⟨t,C,ht,q⟩:= Standby.sum hg; rw [Finset.sum_insert e,Finset.sum_insert e, echo_add i p q hs ht,ih hg]
lemma glean_pool (F:Frame G h)(i:Alma F){P:E→ Single G D}(S:Finset E)(h:∀ j∈S,∀ k r, Standby (P j k r)):glean F (∑ v∈S,P v) e i=∑ v∈S,glean F (P v) e i:=by
    unfold glean; dsimp only; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r hr; by_cases hz:valence F i≤ e+r; · simp only [if_pos hz, Finset.sum_apply]; exact echo_sum F i S (fun j hj=> h j hj ..)
    simp only [if_neg hz,Finset.sum_const_zero]

lemma glean_stake (F:Frame G h)(v:Single G D)(p:∀i r, Standby (v i r))(A: Blue.Cost)(e:ℕ)(i: Alma F): glean F (affix A v) e i=∑ j∈Finset.antidiagonal e, coeff j.1 A * glean F v j.2 i:=by
    let l:=valence F i
    unfold glean; dsimp only; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r hr; have hL:r ≤ l:= Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    by_cases hx:l≤ e+r
    · rw [if_pos hx,affix,Finset.sum_apply]; let S:=Finset.antidiagonal (e+r-l); let v' (j: ℕ ×ℕ):=coeff j.1 A•v j.2 r
      have he : echoS F (∑ j∈ S,v' j) i= ∑ j∈ S,coeff j.1 A *echoS F (v j.2 r) i:= by rw [echo_sum]; exact Finset.sum_congr rfl fun j _=>echo_mu F i _ _; exact fun j _=> (p ..).μ _
      change echoS F (∑ j∈ S,v' j) i=_; rw [he]; set T:=(Finset.antidiagonal e).filter fun j=>l ≤ j.2+r
      rw [←Finset.sum_subset (Finset.filter_subset (fun i:ℕ ×ℕ=>l≤ i.2+r) (Finset.antidiagonal e))]
      · let d:=l-r; refine Finset.sum_bij (fun j _=>(j.1,j.2+d)) (fun j hj=>?_ ) ?_ ?_ ?_
        · have ht:= Finset.mem_antidiagonal.mp hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (show j.1+(j.2+d)=e from by unfold d; omega),show l≤j.2+d+r from by unfold d; omega⟩
        · intro a ha b hb p; have ⟨x,y⟩:= Prod.mk.inj p; exact Prod.ext x (Nat.add_right_cancel y)
        · intro b hb; obtain ⟨x,y⟩:= Finset.mem_filter.mp hb; have x := Finset.mem_antidiagonal.mp x; refine ⟨(b.1,b.2-d),Finset.mem_antidiagonal.mpr ?_, Prod.ext rfl ?_⟩; · change b.1+(b.2-d)= _; unfold d; omega
          change b.2-d+d=b.2; unfold d; omega
        intro j hj; dsimp only; rw [if_pos (show l≤j.2+d+r from by unfold d; omega),show j.2+d+r-valence F i=j.2 by unfold d l; unfold l at hL; omega]
      intro j hj hj'; rw [if_neg (show ¬ l≤ j.2+r from fun h=>hj' (Finset.mem_filter.mpr ⟨hj,h⟩)),mul_zero]
    rw [if_neg hx]; symm; apply Finset.sum_eq_zero; intro i hi; have hh:= Finset.mem_antidiagonal.mp hi; rw [if_neg (show ¬ l≤ i.2+r from by omega),mul_zero]
def prismata (F:Frame G h)(P:Thesis F D): Coil F:= Matrix.of fun i j=> PowerSeries.mk fun k=> glean F (P j) k i
lemma coined (P: Thesis F D)(k i j): lineS (prismata F P) k i j= glean F (P j) k i:=by rw [lineS,Matrix.of_apply,prismata, Matrix.of_apply,coeff_mk]
lemma extortion {A B: Coil F}(p:∀ k i j,lineS A k i j=lineS B k i j): A=B:= by ext1 i j; ext1 k; exact p k i j
lemma prismata_bind (F:Frame G h)(P:Thesis F D)(v:∀ i j k, Standby (P i j k))(A:Coil F): prismata F (impose P A)=prismata F P*A:=by
   refine extortion fun k i j=>?_; rw [coined,impose, glean_pool F _ _ (fun v' _=> Standby.affixed (v v') (A v' j)), line_mul,Matrix.sum_apply]
   simp_rw [Matrix.mul_apply]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro m _; rw [glean_stake F _ (v _)];
   rw [← Finset.Nat.sum_antidiagonal_swap]; apply Finset.sum_congr rfl; intro v _; dsimp only [Prod.swap]; rw [coined,mul_comm]; rfl
lemma billing (F:Frame G h)(P:Thesis F D)(p:∀ i,shellK (valence F i) (P i)): trample F (prismata F P):=by
    intro k i j he; rw [coined]; unfold glean; dsimp only; apply Finset.sum_eq_zero; intro r hr; split; · rw [p j _ _ (by omega),echo_zero]
    rfl
end YM.WilsonCoeffUV.Cosmos
