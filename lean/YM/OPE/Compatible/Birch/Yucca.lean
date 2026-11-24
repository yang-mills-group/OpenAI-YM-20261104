import YM.OPE.Compatible.Birch.Root
/-!
# Family circuit payments. Bananas continuous all metrics, account for arbitrary post polynomial. Weighted itinerary post K. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W:Type*} {i j n r d m:ℕ}{G:Gauge}{s b U D t ε:ℝ}{N:Side}
namespace Script
open Page
variable {K:Type*} {p q:K→Script I r} {X u:K→ℝ}{A B:K→Row I J}
def Loan (m:ℕ)(p:K→Script I r)(u X:K→ℝ):Prop:=∃ c:ℝ,0≤ c∧ ∃ n:ℕ, ∀ i, soot m (p i) (c*(X i^n)*u i)
def Tip (s:ℝ)(p:K→Row I J) (u X: K→ℝ):Prop:=∃ c:ℝ,0 ≤ c∧∃ n:ℕ,∀ i,(p i).strip s (c*(X i^n)*u i)
lemma Loan.bill (h:Loan m p u X)(i):∃ c,soot m (p i) c:=by obtain ⟨c,h,K,g⟩:=h; exact ⟨_,g i⟩
lemma Loan.mild {a:K→ℝ}(h:Loan m p u X)(hp:1 ≤ X)(hv:u ≤ a):Loan m p a X:=by
    obtain ⟨c,hc,n,H⟩:=h; exact ⟨c,hc,n,fun i=>(H i).tips (mul_le_mul_of_nonneg_left (hv i) (mul_nonneg hc (zero_le_one.trans <| one_le_pow₀ (hp i))))⟩
lemma Loan.crush (h:Loan m p u X)(hp:n ≤ m):Loan n p u X:=by obtain ⟨c,hc,K,H⟩:=h; exact ⟨c,hc,K,fun i=> (H i).minor (fun i=>zero_le_one.trans (payer n i)) (fun i=>pow_le_pow_right₀ (show 1 ≤ (stamp i:ℝ) by exact_mod_cast notch_one i.xy) hp) le_rfl⟩
lemma Loan.zero (m n:ℕ): Loan (r:=n) (I:=I) m (fun _:K=>0) u X:= ⟨0,le_rfl,0,fun i=> Sack.zero (by simp) _⟩ -- unused
lemma Loan.seize (h:Loan m p u X)(hp:Loan m q u X)(hx:1≤ X)(hg:0≤ u): Loan m (p+q) u X:=by
    obtain ⟨a,ha,k,H⟩:=h; obtain ⟨b,hb,j,G⟩:=hp; refine ⟨a+b,add_nonneg ha hb,k+j,fun i=>(Sack.splits (H i) (G i) (fun j=>zero_le_one.trans (payer m j))).tips ?_⟩; rw [add_mul, add_mul]; have hx:= show 1≤ X i from hx i; have hu:0≤u i:=hg i; exact add_le_add (by gcongr; omega) (by gcongr; omega)
lemma Loan.cut (h:Loan m p u X):Loan m (-p) u X:=by
    obtain ⟨c,hc,n,H⟩:=h; refine ⟨c,hc,n,fun i=>?_⟩; simpa only [Loan,soot,Sack,Pi.neg_apply,norm_neg] using (H i)
lemma Loan.count [Fintype W](f:W→K→Script I r)(h:∀ i, Loan m (f i) u X)(hp:1 ≤ X)(hg: 0 ≤ u): Loan m (∑ i,f i) u X:=by
    suffices H:∀ v: Finset W,Loan m (∑ i∈v,f i) u X from H _; intro v; induction v using Finset.induction_on with
    | empty=>simp only [Finset.sum_empty]; exact Loan.zero ..
    | insert i s hi ih=> rw [sum_insert hi]; exact (h i).seize ih hp hg
lemma Loan.scaleL (h:Loan m p u X)(x:ℝ): Loan m (x • p) u X:=by
    obtain ⟨c,hc,n,H⟩:=h; refine ⟨‖x‖*c,by positivity,n,fun i=> ((H i).scale_line _).tips ?_⟩;exact le_of_eq (by ring)
lemma Loan.decoys (s:Equiv.Perm (Fin r))(h:Loan m p u X): Loan m (fun i=>swing s (p i)) u X:= by obtain ⟨c,hc,n,H⟩:=h;exact ⟨c,hc,n,fun i=> swing_fee (H i) s⟩
lemma Loan.twirl (h:Loan m p u X):Loan m (fun i=>bouquet (p i)) u X:=by obtain ⟨c,hc,n,H⟩:=h; exact ⟨c,hc,n,fun i=> adjusted (H i)⟩
lemma Loan.land (h:Loan m p u X):Loan m (fun i=>silt (p i)) u X:=by obtain ⟨c,hc,n,H⟩:=h; refine ⟨((r+1:ℕ):ℝ)^m*c,by positivity,n,fun i=>(silt_cost (H i)).tips ?_⟩;exact le_of_eq (by ring)
lemma bouquetSub {p q:Script I r}: bouquet (p-q)= bouquet p-bouquet q:=by
    unfold bouquet; rw [← smul_sub,← Finset.sum_sub_distrib];rfl
lemma Loan.stilt (h:Loan m p 1 X)(hp:Loan m q 1 X)(hv:Loan m (p-q) u X) : Loan m (fun i=>stitch (p i)-stitch (q i)) u X:=by
    have hh :=hv.twirl.land; rw [show (fun i=>stitch (p i)-stitch (q i))= _ from ?_]; exact hh
    ext1 i; exact ((show silt (bouquet (p i-q i))= _ from by rw [bouquetSub,silt_sub (sootS (h.twirl.bill i|>.choose_spec)) (sootS (hp.twirl.bill i|>.choose_spec))];rfl)).symm
end Script
end YM.OPE.Flume
