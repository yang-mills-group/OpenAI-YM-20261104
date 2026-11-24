import YM.WilsonCoeffUV.Root.Post.SlotLease
/-!
# Slot-charge matrix algebra. X is common at one step.
Offdiag event support for ordered inverse, pre bound in each slot.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}

abbrev Wall (F:Frame G h):= Matrix (Alma F) (Alma F) ℝ
abbrev Coil (F:Frame G h):= Matrix (Alma F) (Alma F) (PowerSeries ℝ)
def lineS (A:Coil F)(k:ℕ): Wall F:=Matrix.of (fun i j =>coeff k (A i j))
lemma line0 (A:Coil F): lineS A 0= (constantCoeff (R:=ℝ)).mapMatrix A:= by ext i j; exact coeff_zero_eq_constantCoeff_apply ..
lemma line_mul (A B:Coil F)(i:ℕ): lineS (A*B) i=∑ j∈Finset.antidiagonal i,lineS A j.1*lineS B j.2:=by
    ext x y; unfold lineS; simp_rw [Matrix.sum_apply, Matrix.of_apply, Matrix.mul_apply, map_sum, coeff_mul]; exact Finset.sum_comm

def highUp (F:Frame G h)(i:Alma F) := (h-valence F i)*(h+1)+weight F i
def ceiling (h:ℕ):= h*(h+1)+h+1
lemma high_lt (i:Alma F): highUp F i < ceiling h:= by unfold highUp ceiling; apply Nat.lt_succ_of_le; exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le ..)) (weigh_cap ..)
lemma rise_slot (i j: Alma F)(h':valence F i< valence F j): highUp F i> highUp F j:=by
    let a:=h-valence F i; let b:=h-valence F j; have hb:b+1≤ a:=by unfold a b; have ht:= valence_cap F j; omega
    change b*(h+1)+weight F j<a*(h+1)+_; refine lt_of_lt_of_le ?_ (Nat.le_add_right ..); apply Nat.lt_of_lt_of_le _ (Nat.mul_le_mul_right (h+1) hb); rw [add_mul,one_mul]; have H:= weigh_cap F j; omega
def matPow (n:Side)(i:Alma F):= (n.val:ℝ)^(h-weight F i)
lemma matPow₁ (n:Side)(i:Alma F): 1≤ matPow n i:= one_le_pow₀ (by exact_mod_cast n.property)
def Tram (F:Frame G h)(c:ℕ)(A:Wall F): Prop:= ∀ i j:Alma F, valence F j + c<valence F i → A i j=0
def leaseM (n:Side)(F:Frame G h)(A:Wall F): Prop:= Tram F 0 A ∧∀ i j, valence F i=valence F j → weight F i ≤ weight F j → A i j= if i=j then matPow n j else 0
def trample (F:Frame G h)(A:Coil F):Prop:=∀ k,Tram F k (lineS A k)
lemma Tram.mul {A B:Wall F}(h:Tram F k A)(p:Tram F l B): Tram F (k+l) (A*B):=by
    intro i j v; rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro b _; by_cases e: valence F b+k < valence F i; · rw [h i b e,zero_mul]
    rw [p b j (by omega),mul_zero]
lemma Tram.one : Tram F k 1:=by
    intro i j h; rw [Matrix.one_apply_ne]; intro p; subst j; omega
lemma Tram.zero : Tram F k 0:= by intro i j h; rfl
lemma Tram.neg {A:Wall F}(p:Tram F k A): Tram F k (-A):=by intro i j v; simp [p i j v]
lemma Tram.sum {S:Finset U}{A:U→ Wall F}(p:∀i∈ S,Tram F k (A i)):Tram F k (∑ i∈S,A i):=by
    intro i j v; rw [Matrix.sum_apply]; exact Finset.sum_eq_zero (fun b h=>p b h i j v)
lemma Tram.add {A B:Wall F}(p:Tram F k A)(q: Tram F k B): Tram F k (A+B):=by intro i j v; rw [Matrix.add_apply,p i j v,q i j v,zero_add]
lemma Tram.power {A: Wall F}(h:Tram F 0 A)(k): Tram F 0 (A^k):=by induction k with
                                                                                | zero=> rw [pow_zero]; exact Tram.one
                                                                                | succ k ih=> rw [pow_succ]; exact ih.mul h
def rapid (F:Frame G h)(k:ℕ)(A:Wall F): Prop:= ∀ i j, highUp F i < highUp F j+k → A i j=0
lemma rapid.power {A:Wall F}(p:rapid F 1 A)(k:ℕ): rapid F k (A^k):=by
    induction k with
    | zero=> rw [pow_zero]; intro i j v; rw [Matrix.one_apply_ne]; intro h; subst j; omega
    | succ k ih=>
       intro i j v; rw [pow_succ,Matrix.mul_apply]; apply Finset.sum_eq_zero; intro t _; by_cases h: highUp F i<highUp F t+k; · rw [ih i t h,zero_mul]
       rw [p t j (by omega),mul_zero]
-- normalize by slot matrix on RIGHT
abbrev saddle (n:Side)(F:Frame G h): Wall F := Matrix.diagonal (fun i=> (matPow n i)⁻¹)
lemma Tram.sad (F:Frame G h)(n:Side): Tram F k (saddle n F):=by
    intro i j v; by_cases h:i=j; · subst j; omega
    simp [saddle,h]
def negNest (A:Wall F)(L:Side):= 1-A*saddle L F
lemma Tram.nesting {L:Side}{A:Wall F}(p:Tram F 0 A): Tram F 0 (negNest A L):= by unfold negNest; rw [sub_eq_add_neg]; exact Tram.one.add (p.mul (Tram.sad (k:=0) F L)).neg
lemma rapid.nesting {L:Side}{A: Wall F}(p:leaseM L F A): rapid F 1 (negNest A L):=by
   intro i j v; by_cases h : i=j
   · subst j; have he:= p.2 i i rfl le_rfl; have ht : matPow L i>0:=zero_lt_one.trans_le (matPow₁ ..); simp [negNest,saddle,he,ht.ne']
   suffices hv:A i j=0 from by simp [negNest,saddle,h,hv]
   by_cases e:valence F i=valence F j
   · have H:= p.2 i j e (by unfold highUp at v; rw [e] at v; omega); rwa [if_neg h] at H
   have h : ¬ valence F i<valence F j:= fun H=> False.elim (by have hp:=rise_slot i j H; omega); exact p.1 i j (by omega)
def hamp (A:Wall F)(L:Side): Wall F:= ∑ i∈ Finset.range (ceiling h), negNest A L^i
def steed (A:Wall F)(L:Side): Wall F:= saddle L F*hamp A L
lemma recognition {A:Wall F}(p:leaseM n F A): A*steed A n=1 := by
   let V:=negNest A n; have hZ:V^ceiling h=0:= Matrix.ext (fun i j=> (rapid.nesting p).power _ i j (by have H:=high_lt i; omega))
   unfold steed hamp; rw [← Matrix.mul_assoc, show A*saddle n F= -(V-1) by unfold V negNest; abel,neg_mul]; change -( (V-1) *∑ i∈ Finset.range (ceiling h), V^i)=1; rw [mul_geom_sum V (ceiling h),hZ,zero_sub,neg_neg]
lemma trove {A:Wall F}(p:leaseM n F A): IsUnit A.det:= Matrix.isUnit_det_of_right_inverse (recognition p)
lemma steed_value {A:Wall F}(p:leaseM n F A): A⁻¹= steed A n:= by
    have hv:= recognition p; calc
       A⁻¹=A⁻¹*(A*steed A n):= by rw [hv,_root_.mul_one]
       _=steed A n:=by rw [← Matrix.mul_assoc,nonsing_inv_mul A (trove p),_root_.one_mul]
lemma Tram.elastic {A:Wall F}(p:leaseM n F A): Tram F 0 (A⁻¹):=by rw [steed_value p,steed,hamp]; exact (Tram.sad F n).mul (Tram.sum (k:=0) (fun i _=> (Tram.nesting p.1).power _))
lemma stellarized {A:Coil F}(p:leaseM n F (lineS A 0)): IsUnit A.det:=by
   rw [PowerSeries.isUnit_iff_constantCoeff,RingHom.map_det, ←line0]; exact trove p
lemma line_steed {A:Coil F}(p:leaseM n F (lineS A 0)): lineS A⁻¹ 0 = steed (lineS A 0) n:=by
    have he: lineS A 0*lineS A⁻¹ 0=1:=by rw [line0,line0, ←map_mul, Matrix.mul_nonsing_inv A (stellarized p),map_one]
    rw [← steed_value p]; exact (Matrix.inv_eq_right_inv he).symm
lemma choral (F:Frame G h) (k:ℕ)(p:k>0): lineS (1:Coil F) k=0:=by ext1 i j; by_cases h:i=j <;> simp [lineS,h,p.ne']
lemma tiller {A:Coil F}(p:leaseM n F (lineS A 0))(h:trample F A): trample F A⁻¹:=by
    let f:=lineS A; let g:=lineS A⁻¹
    have hg:g 0 = (f 0)⁻¹:= (line_steed p).trans (steed_value p).symm
    intro k; induction k using Nat.strong_induction_on with
    | h i ih=>
       change Tram F _ (g _); by_cases hx:i=0; · rw [hx,hg]; exact Tram.elastic p
       have hv: lineS (A*A⁻¹) i=0:=by rw [Matrix.mul_nonsing_inv A (stellarized p)]; exact choral F i (by omega)
       let T:= (Finset.antidiagonal i).erase (0,i); have ht : (0,i)∈ Finset.antidiagonal i:= Finset.mem_antidiagonal.mpr (Nat.zero_add _)
       let Q:= ∑ j∈ T,f j.1*g j.2
       rw [line_mul,← Finset.add_sum_erase (Finset.antidiagonal i) _ ht] at hv
       rw [show g i=(f 0)⁻¹*(-Q) from Eq.trans (Eq.symm (Matrix.nonsing_inv_mul_cancel_left _ _ (trove p))) (congr_arg ((f 0)⁻¹*·) (eq_neg_of_add_eq_zero_left hv))]
       have he: Tram F i Q:= Tram.sum (fun j hj=>by
          obtain ⟨hx,x⟩:= Finset.mem_erase.mp hj; have hp:=Finset.mem_antidiagonal.mp x
          have hv : j.2< i:= by by_contra! H; exact hx (Prod.ext (show j.1=0 from by omega) (show j.2=i from by omega))
          exact hp ▸ ((h j.1).mul (ih j.2 hv)))
       simpa only [Nat.zero_add] using (Tram.elastic p).mul he.neg
end YM.WilsonCoeffUV.Cosmos
