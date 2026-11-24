import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Sync
/-!
# Hessian pairing equals Q_BV
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{n:ℕ} {U V:Mield G n}{F H:Rack G n} (p:SectorP n) (x:Cfield G n) (a b:Chan G n)
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local notation "K" => ploy G 0 n
local notation "Q" =>  Plane.Charge.table (Wick.Q G n)
lemma moss (w:Legs ( Shore G n) ) : phase a * K ((onX true a,p)::w) = applyS 0 G n a w:= by
    unfold ploy; simp only [Pi.add_apply]; rw [ show core G n 0 ( (onX true a,p)::w)=0 from congr_fun ((core_g (G:=G) (n:=n) 0).2.1 a p) w, zero_add]; rw [D_eval (onX true a,p) (cape (applyS 0 G n)), cape_tick (application 0)]; simp only [Pi.smul_apply,smul_eq_mul,← mul_assoc,phase2,one_mul]
lemma s_a : applyS 0 G n a [(x,p)]= Q x (onX false a) p:= by
   rcases a with ⟨_|a,i⟩; · unfold applyS Wick.Q; simp only [Sc,neg_zero,zero_div,zero_smul,Pi.zero_apply]; unfold send choir; dsimp only; split; swap; rfl; rcases x with ⟨⟨_|c,_|_⟩,b⟩ <;> rfl
   unfold applyS convoke; simp only [zero_smul, add_zero]; unfold axisP; rw [lock,rowP,moon];
   simp only [cwave,lip,leaf,node1,net_cons, show net (A:= Cfield G n) ([]: Legs (Shore G n))=0 from rfl, add_zero]; rcases x with ⟨⟨_|x,_|_⟩,j⟩ <;> simp [Wick.Q,send,choir,bare, onX,spike_δ,spikeV,mul_ite]
lemma wan0 : cape ( applyS 0 G n ) [(onX false a,-p),( onX false b,p )]=0 := by
   unfold cape; simp only [ Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_eq_zero; intro i _; simp_rw [ pairv ( mon_leaf ( onX true i )) (m_apply i), leaf,node1]; simp [onX]
lemma tab_s (u:Bool) : phase a * K [( onX (!u) a,-p),( x,p )]= Q x (onX u a) p := by
    cases u with
    | false=>
       exact ( moss (-p) a [(x,p)] ).trans (s_a p x a)
    | true=>
       let l:=x; rcases x with ⟨⟨q,_|_⟩,k⟩
       · change phase a*( core G n 0 [(onX false a,-p),(onX false (q,k),p)]+ cape (applyS 0 G n) [(onX false a,-p),(onX false (q,k),p)])= Q _ _ _; rw [wan0 p a (q,k),add_zero]; rcases a with ⟨_|a,i⟩
         · rw [weak_l]; -- parser
           cases q <;> simp [Wick.Q, send,choir,bare,onX]; exact Or.inl (by simp [onX,at_g])
         cases q with| none=> rw [weak_l]; simp [Wick.Q, send,choir,bare,onX]; exact Or.inr (by simp [onX,at_g])| some q=> change phase (G:=G) (n:=n) (some a,i)*core G n 0 [(at_g a i,-p),(at_g q k,p)]=_; rw [kernel]; simp [phase,Wick.Q,send,choir,bare,onX,realK (i:=a) (j:=q),eq_comm (a:=k)]
       change phase a * K [( onX false a,-p),( onX true (q,k), p )]= Q ( onX true (q,k)) (onX true a) p; rw [show K [(onX false a,-p),(onX true (q,k),p)] = cross (parity ( onX false a)) ( parity (onX true (q,k))) * K [(onX true (q,k),p),(onX false a,-p)] from ploy_sym [] (onX false a,-p) _ []]; rw [show K [(onX true (q,k),p),(onX false a,-p)]= phase (n:=n) (q,k) * Q (onX false a) (onX false (q,k)) (-p) from ?_]; rotate_left; · rw [ ← s_a,← moss p, ← mul_assoc, phase2,one_mul]
       rcases a with ⟨_|a,i⟩ <;> cases q <;> simp [phase, Wick.Q,send,choir,bare,onX,mul_ite,parity,Landau.p,cross, eq_comm (a:=k)]
lemma inning (l:Legs (Shore G n)) (F:Rack G n): attaches parity ( Wick.D0 G n ) K F [(x,p)] l= solos (Wick.Q G n) F [(x,p)] l:= by -- Σ x,y.Eval. hp.E.
    rw [ convertR ( Wick.reverse_d G n ) ]; let iq:= (x,p); let U:= radius Landau.parity (Wick.D0 G n) ; let T:= fun i:Cfield G n=> ∑ j:Cfield G n, U j i K F [iq] l; have ht (f:Cfield G n→ℂ): ∑ i,f i= ∑ i:Bool,∑ k:Chan G n, f (onX i k):= by rw [ ← Equiv.sum_comp (split0' G n).symm f,Fintype.sum_prod_type]; rfl
    change _ = ∑ j:Cfield G n,Q x j p * F ((j,p)::l); rw [Finset.sum_comm,ht, ht (fun j:Cfield G n=>Q x j p * F ((j,p)::l))]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; simp_rw [ht (fun j'=> radius parity ( Wick.D0 G n ) j' _ K F _ _),blastD _ _ _ _ _ _ (ploy_p 0)]; unfold glow0; simp only [net_cons,show net (A:=Cfield G n) ([]:Legs (Shore G n))=0 from rfl,add_zero, tab_s]; cases i <;> simp
lemma φQ (h:Symm S F): tree parity ( Wick.D0 G n ) K F= (Wick.Q G n).raise F:= singleFac _ (s2_rank G n) _ _ (fun ⟨i,j⟩ k=> inning j i k F) h
end YM.MS.Motif
