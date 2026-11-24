import YM.RegulatorIR.Cluster.Costing

/-! Uniform inhomogeneous evolution: force in powers of the heat parameter
k on *the product*. d,d^-1 admissible. Pre-Λ repeated Ward cost not used
here, only for further running. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Set Function Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Diagram Collapsed
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W : Type}{X : W→ Type}{L:Meter W}{v w:W→ℝ≥0∞}{d l:W→ℝ}{hl:∀ i,0<l i}{x:(i:W)→X i→ Room}{S T:W→Set Room}{u b p k r e m n:ℕ}

namespace Collapsed
def groupUp (S T:W→Set Room)(i:W):= S i∪ T i
def pledge (v w:W→ℝ≥0∞) (d l:W→ℝ) (b:ℕ) (i):= v i*w i*(amount (l i) b (d i))⁻¹
variable {K:∀ i,Layer (X i) (X i)} {A B C:∀ i,Orders (X i)}
lemma clot {U:(i:W)→Packet (X i) (m+1)}{V:(i:W)→Packet (X i) (n+1)}(h:∀ i,Remotely (S i) (T i) (d i))(hh:Beam L (home hl x (u+b)) K)
  (ht:Claim L (estate hl x S (u+b)) v U)(hv:Claim L (estate hl x T (u+b)) w V)(hx:∀ i,0≤ d i): Claim L (estate hl x (groupUp S T) u) (pledge v w d l b) (fun i=> Packet.knot (K i) (U i) (V i)) := by
 obtain ⟨c,hc,H⟩:=hh
 let O i:= markQ (estate hl x (groupUp S T) u i) (Packet.knot (K i) (U i) (V i)); let f i:= amount (l i) b (d i)
 have hQ: Carry L (fun i=> v i*w i) (fun i=> O i*f i):= Carry.mono (ticket_times ht (Carry.mul_right hv hc)) fun i=> away (h i) _ _ _ _ (show row (swap (K i)) (native _ (hl i) _) (x i) (x i) (c i) from (H i).2)
 apply Carry.mono (Carry.scale (w:=fun i=>(f i)⁻¹) hQ)
 intro i
 change O i≤ O i*f i*(f i)⁻¹
 have hz:f i≠0 := (lt_of_lt_of_le zero_lt_one (amount_unit (hl i) _ (hx i))).ne'
 have ht:f i≠⊤:= by unfold f amount; finiteness
 rw [mul_assoc,ENNReal.mul_inv_cancel hz ht,mul_one]
end Collapsed
open Collapsed
variable {K:∀ i,Layer (X i) (X i)} {A B C:∀ i,Orders (X i)}

-- Total_mark/Yield to families

def treatment (K:∀ i:W,Layer (X i) (X i))(C A:∀ i,Orders (X i))(f:Bool) i:=markHeat (K i) (logHeat (K i) (C i) f) (A i)

structure Fund (p:ℕ)(L:Meter W)(hl:∀ i,0<l i)(x:(i:W)→ X i→Room) (u:ℕ) (C:∀ i,Orders (X i))(K:∀ i,Layer (X i) (X i)): Prop where
 vac : ∀ i,Vacuum (C i)
 work : ∀ i ≤ p, ∀ j,Workday L (home hl x u) (fun w=> C w i j)
 beam : Beam L (home hl x u) K
 alignment : ∀ i,gradedSymmetric (C i)
 matrix : ∀ i v w,K i v w=K i w v
namespace Fund
lemma controls (G:Fund p L hl x u C K) (i)(f:Bool): Cost (logHeat (K i) (C i) f) p:=by
 intro k e he j; obtain ⟨g,hg,H⟩:=Workday.hot G.work G.beam f k e (j+1) he; exact held_enough _ _ (H i) (hg.cost _)
lemma station {a:ℕ}(G:Fund p L hl x a C K)(A':Folds p L (estate hl x S u) v A)(f:Bool)(ht:u ≤ a)(k): Folds p L (estate hl x S u) v (fun w=>treatment K C A f w k):= Cluster.stays K A' (shorter S ht G.beam) G.vac (fun i hi r=>overnight S ht (G.work i hi r)) f k
lemma price {a:ℕ}(G:Fund p L hl x a C K)(A':Folds p L (estate hl x S u) v A)(f:Bool)(ht:u ≤ a)(hc:∀ i,v i≠⊤)(i): Price (treatment K C A f i) p:=fun k=> ((G.station A' f ht k).pay hc i)
end Fund

structure Widths {l:W→ℝ}(p:ℕ)(L:Meter W)(hl:∀ i,0<l i)(x:(i:W)→X i→Room) (d:W→ℝ) (S T:W→ Set Room) (u b m n:ℕ)(v w:W→ℝ≥0∞)(A B: (i:W)→Orders (X i)):Prop where
 rays : ∀ i,Remotely (S i) (T i) (d i)
 nonneg : ∀ i,0 ≤ d i
 limit₁ : ∀ i,v i≠⊤
 limit₂ : ∀ i,w i≠⊤
 pay₁ : Folds p L (estate hl x S (u+b)) v A
 pay₂ : Folds p L (estate hl x T (u+b)) w B
 rank₁ : ∀ i,Ranks m (A i)
 rank₂ : ∀ i,Ranks n (B i)
 sort₁ : ∀ i,gradedSymmetric (A i)
 sort₂ : ∀ i,gradedSymmetric (B i)
namespace Widths
variable (I:Widths p L hl x d S T u b m n v w A B)(G:Fund p L hl x (u+b) C K)
include I
lemma union_price : Folds p L (estate hl x (groupUp S T) (u+b)) (fun i=> v i*w i) (fun i=>accord (A i) (B i)):= Folds.times (Folds.lesser (u+b) (fun i=>(I.rays i).awake) (fun _=>subset_union_left ..) I.pay₁) (Folds.lesser (u+b) (fun i=>(I.rays i).overT) (fun _=>subset_union_right ..) I.pay₂)
lemma union_money {E:∀ w,Tariff (X w)}{H : (w:W)→Premium (E w)} (F:Folds p L H (fun i=>v i*w i) A) (i): Bill (A i) p:= F.pay (fun i=> ENNReal.mul_ne_top (I.limit₁ i) (I.limit₂ i)) i
include G
lemma leap (f:Bool): Folds p L (estate hl x (groupUp S T) u) (pledge v w d l b) fun i=> drift (K i) (treatment K C A f i) (treatment K C B f i) k:=by
 intro e he r; unfold drift carry force; apply Claim.sum; intro a _;apply Claim.sum;intro b hb;apply Claim.sum;intro c hc
 have hp:= Finset.mem_antidiagonal.mp hb; have hu:=Finset.mem_antidiagonal.mp hc;subst r; simp only [matchTwo]
 refine Claim.csmul (Claim.robust ?_) _
 exact clot I.rays G.beam (G.station I.pay₁ f le_rfl a.1 b.1 (by omega) (c.1+1)) (G.station I.pay₂ f le_rfl a.2 b.2 (by omega) (c.2+1)) I.nonneg

def impact (A B C:(i:W)→Orders (X i))(K:∀ i,Layer (X i) (X i)) (f:Bool)(i : W): Rhythm (X i):= clash (A i) (B i) (logHeat (K i) (C i) f) (K i)
lemma equation (f:Bool) (i:W)(he:e ≤ p): let P:=impact A B C K f i; let V:= logHeat (K i) (C i) f; let s:=(treatment K C A f i); let t:=treatment K C B f i; P (k+1) e r= ((k+1:ℝ)⁻¹) • ((heating (K i) (P k e) r+ drift (K i) P V k e r)+drift (K i) s t k e r):=by
 intro P V s t; obtain ⟨c,hc,H⟩:= G.beam
 have hp := wave (k:=k) (G.vac i) (G.alignment i) (I.rank₁ i) (I.rank₂ i) (I.sort₁ i) (I.sort₂ i) (G.matrix i) (H i).1 (hc.cost i) he (G.price I.pay₁ f le_rfl I.limit₁ i) (G.price I.pay₂ f le_rfl I.limit₂ i) (G.price I.union_price f le_rfl (fun i=> ENNReal.mul_ne_top (I.limit₁ i) (I.limit₂ i)) i) (G.controls i f)
 rw [show heating (K i) (P k e) r+drift (K i) P V k e r +drift (K i) s t k e r=(k+1:ℝ) • P (k+1) e r from (congr_fun hp r).symm, smul_smul,inv_mul_cancel₀ (by positivity : (k:ℝ)+1≠0),one_smul]
lemma first_joins (f:Bool)(k:ℕ): Folds p L (estate hl x (groupUp S T) u) (pledge v w d l b) (fun i=>impact A B C K f i k):=by
 let H:=estate hl x (groupUp S T) u;let D:(i:W)→ Tariff (X i):=fun i=> (fare (hl i) u (groupUp S T i)).uses (x i)
 have ht: Beam L D K:= shorter (groupUp S T) (by omega) G.beam
 induction k using Nat.strong_induction_on with
 | _ k ih=>
   cases k with
   | zero=>
      intro e _ r
      have h' i (t:ℕ): impact A B C K f i 0 t r=0:=by unfold impact;rw [crest]; rfl
      simp_rw [h'];exact Claim.zeroQ
   | succ k=>
      intro e he r
      simp_rw [equation I G f _ he]
      apply Claim.csmul; apply Claim.add _ (leap I G f e he r)
      apply Claim.add (Claim.with_heat (ih k (by omega) e he (r+2)) ht)
      unfold drift carry force; apply Claim.sum;intro a ha;apply Claim.sum;intro q hq; apply Claim.sum; rintro ⟨i,j⟩ _
      have he':= Finset.mem_antidiagonal.mp ha;have hx:= Finset.mem_antidiagonal.mp hq; exact Claim.with_match r i j ht (ih a.1 (by omega) q.1 (by omega) (i+1)) (Workday.hot (fun i hi r=>overnight (groupUp S T) (by omega) (G.work i hi r)) ht f a.2 q.2 _ (by omega))
end Widths
end YM.RegulatorIR.Cluster
