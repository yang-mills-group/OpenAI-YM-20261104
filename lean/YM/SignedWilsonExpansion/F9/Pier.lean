import YM.SignedWilsonExpansion.F9.Tuition
import YM.SignedWilsonExpansion.F9.BackRow
/-!
# The complete `pier` rank bill

Install is realized once after pre-electing the costs; R-window adjustable to
any of those fixed-rate purchases. Consumers here use bounds at every seat
OR label of the active Rank without re-election. Use Pʰ step in the current
clock and for finite horizons price the count of the entire window by the
same X (no brightness assumed along windows too long for the activated crop).
Xh convention (X itself before palette or input costs) exposes the independent
powers. This file gives single order/rank recursion.
-/
set_option autoImplicit false
set_option maxHeartbeats 670000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries Supply Ticket Polestar
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m c N u e i j l r q:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {x b B M X Y z:ℝ}{Q:SectionData F}{U:Type*}{E W:Credit}{R:Realm G (q+1) E}

abbrev linkL (A:Levels G)(m c:ℕ):ℝ:= A.S.a m / A.S.a c
def pier (A:Levels G)(Ñ:ChartRatio G)(N h k c m:ℕ)(P:Era G ℝ): Era G ℝ:= linkL A m c ^ h • cruises A Ñ N k c m P
lemma pier_top (P:Era G ℝ): pier A Ñ N h k c c P=P:=by unfold pier linkL; rw [div_self (A.S.a_pos _).ne',one_pow,one_smul,cruises_top]
lemma piered (g:G.Simple)(q:LocalRatio Ñ)(v:m≤c)(hp:c≤N){P:Era G ℝ}(hP:Auth k P): Auth k (pier A Ñ N h k c m P):= (cruising A g q v hp hP).μ _
lemma link_step (A:Levels G)(m c:ℕ): linkL A m c= (A.S.block m).val*linkL A (m+1) c:=by unfold linkL; rw [A.S.a_step]; field_simp
lemma pier_step (g:G.Simple)(q:LocalRatio Ñ)(v:m<c)(hp:c≤ N){P:Era G ℝ}(hP:Auth k P): pier A Ñ N h k c m P=pointStep A Ñ m N h k (pier A Ñ N h k c (m+1) P):=by
    unfold pier; rw [link_step, mul_pow, cruises_sub A Ñ N k P v,step_μ g (v.trans_le hp) q _ (cruising A g q v hp hP),pointStep,smul_comm, smul_smul]
lemma pier_sub (g:G.Simple)(q:LocalRatio Ñ)(v:m≤c)(hp:c≤N){P Q:Era G ℝ}(hP:Auth k P)(hQ:Auth k Q): pier A Ñ N h k c m (P-Q)=pier A Ñ N h k c m P-pier A Ñ N h k c m Q:=by
    induction v using Nat.decreasingInduction with
    | self=> rw [pier_top,pier_top,pier_top]
    | of_succ i s ih=> rw [pier_step g q s hp (hP.sub hQ), ih,step_sub g (s.trans_le hp) q _ _ (piered g q s hp hP) (piered g q s hp hQ),←pier_step g q s hp hP, ←pier_step g q s hp hQ]
lemma pier_sum (g:G.Simple)(q:LocalRatio Ñ)(v:m≤c)(hp:c≤N){J:Type*}(S:Finset J)(f:J→ℝ)(P:J→Era G ℝ)(x:∀ i∈S,Auth k (P i)): pier A Ñ N h k c m (∑ i∈S,f i • P i)=∑ i∈ S, f i • pier A Ñ N h k c m (P i):=by
    induction v using Nat.decreasingInduction with
    | self=> simp_rw [pier_top]
    | of_succ i s ih=> rw [pier_step g q s hp (Auth.sum (fun i hi=>(x i hi).μ _)),ih,step_sum g (s.trans_le hp) q S _ (fun j hj=> piered g q s hp (x j hj))]; exact Finset.sum_congr rfl (fun i hi=> congr_arg (f i • ·) (pier_step g q s hp (x i hi)).symm)
lemma pier_add (g:G.Simple)(q:LocalRatio Ñ)(v:m≤c)(hp:c≤N){P Q:Era G ℝ}(hP:Auth k P)(hQ:Auth k Q): pier A Ñ N h k c m (P+Q)=pier A Ñ N h k c m P+pier A Ñ N h k c m Q:=by apply eq_add_of_sub_eq; rw [←pier_sub g q v hp (hP.add hQ) hQ,add_sub_cancel_right]
-- λ variable count companions
structure Chartage (Q:SectionData F)(A:Levels G)(Ñ:ChartRatio G)(m c N k u e:ℕ)(X:ℝ): Prop where
    simple:G.Simple
    ratios: LocalRatio Ñ
    order:h≤ k
    length:m≤ c
    cap:c≤N
    pos:1≤X
    age:↑(c-m) ≤ X -- nat
    ample: Ample h u (k+e)
    pays (j i r:ℕ): m≤ j → j<c → i≤e → r≤k+e → Report A Ñ Q j N k i u r X
lemma Ample.more {u:ℕ}(q:Ample h u r)(p:l≤r): Ample h u l:= ⟨q.all,(Nat.mul_le_mul_left _ p).trans q.ranks,q.floor⟩

lemma cover (P:Master H) (h k e u V:ℕ)(he:h≤k)(p:u≤ V)(hp:k+e≤ V)(q:Ample h u (k+e)):
    ∃ C:Credit,∀ z:ℝ,1≤ z → ∀ L : Realm G (e+1) Credit.leanC,Install H P L V→∀ m c N:ℕ,L.anchor≤m→ m≤c→ c≤N→ PadRank L m c z→ Chartage (P.T h) L.draws L.paid m c N k u e (C.buy z):=by
    classical
    let Q:= P.T h
    let T:=Fin (e+1); let R:=Fin (k+e+1); let K (v:T×R):= v.2.val; let S (v:T×R):=q.more (Nat.le_of_lt_succ v.2.isLt)
    choose X ψ using fun v:T×R=> assembly Q (P.spec h) (P.pop h) (S v) he v.1.val e Credit.leanC Credit.leanC Credit.leanC (Nat.le_of_lt_succ v.1.isLt)
    obtain ⟨Z,w⟩:= uniformPays (P:=fun i Z=>∀ y:ℝ,1≤ y→(X i).buy y≤ Credit.buy Z y) Finset.univ (fun i _=>⟨X i,fun _ _=>le_rfl⟩) (fun _ _ _ _ h p i v=>(p i v).trans (h i v))
    let C:= Z.plus Credit.leanC; refine ⟨C,fun z hz L f m c N hv hw hh hm=>?_⟩; refine ⟨L.hG,L.green,he,hw,hh,C.purchase hz,hm.lengthS.trans (by simpa using Credit.thickened Z (V:=Credit.leanC) hz),q,?_⟩
    intro j i r u s v t; let x:T×R:=(⟨i,Nat.lt_succ_of_le v⟩,⟨r,Nat.lt_succ_of_le t⟩); have ha:= hv.trans u
    obtain ⟨I,hs,H⟩:= f.aim h (by omega) j ha
    exact (ψ x L (f.bed k (by omega) _ p) j N I ha (s.trans_le hh) hs (H ⟨k,by omega⟩ ⟨_,Nat.lt_succ_of_le p⟩ ⟨r,Nat.lt_succ_of_le (t.trans hp)⟩ i v (S x))).raise ((((X x).elder (L.depth _ ha) (hm.year j u s.le)).trans (w _ (Finset.mem_univ _) z hz)).trans (Credit.thickens _ hz))

lemma staff (p:Report A Ñ Q m N k i u r x): Down (wT F) (stepT Q A Ñ m k N r) x:=
    ⟨fun i => by rw [p.top i i le_rfl,if_pos rfl]; exact one_le_pow₀ (by exact_mod_cast (A.S.block m).pos),p.fare,fun i j u h=>(p.top i j u).trans (if_neg h) ⟩
namespace Chartage
variable (w:Chartage Q A Ñ m c N k u p X)
include w
lemma clip (hm:m≤l)(ht:l≤r)(hv:r≤c): Chartage Q A Ñ l r N k u p X:=⟨w.simple,w.ratios,w.order,ht,hv.trans w.cap,w.pos,(Nat.cast_le.mpr (show r-l≤c-m by omega)).trans w.age,w.ample,fun i j r q u=>w.pays i j r (hm.trans q) (u.trans_le hv)⟩
end Chartage

/-- the back-price alone doesn't claim a bound on *large* rank-r movement
against old coordinates (may be much bigger than this row price). -/
lemma priceBack (F:Frame G h)(r:ℕ)(E W:Credit): ∃ D:Credit,∀ Q:SectionData F,∀ A:Levels G,∀ Ñ k u p m c N X M,1≤X→ 0≤ M→ ∀ e:ℕ, e≤p → r≤k+p → Chartage Q A Ñ m c N k u p X→ ∀ P: Era G ℝ,Auth k P → (∀ j,m≤ j→ j≤c→ Earlier (pier A Ñ N h k c j P) e r u (E.buy X*M)) →(∀ i:TagIx F r, ‖row F ((pier A Ñ N h k c m P).2 e r) i‖ ≤ W.buy X*M) → ∀ i:TagIx F r,∀ j,m≤ j→ j≤c → ‖row F ((pier A Ñ N h k c j P).2 e r) i‖ ≤ D.buy X*M:=by
    let K:=(Credit.leanC.prodC E).plus W; obtain ⟨D,H⟩:= triangular (fun i:TagIx F r=>wT F i) (h+1) K Credit.leanC
    refine ⟨D,fun Q A Ñ k u p m c N X M hx he e h0 r0 w P v f g i j t z=>?_⟩; let V j:= pier A Ñ N h k c j P; let τ j:=row F ((V j).2 e r)
    have hM: 0≤ E.buy X*M:= mul_nonneg (zero_le_one.trans (E.purchase hx)) he
    refine H X hx M he m c w.length w.age (fun j=>stepT Q A Ñ j k N r) τ ?_ ?_ (fun i=> (g i).trans (mul_le_mul_of_nonneg_right (Credit.thickened _ hx) he)) j i (Nat.lt_succ_of_le (F.bound _)) t z
    · intro i hi; rw [Credit.lean_cost]; exact staff (w.pays i _ _ hi.1 hi.2 h0 r0)
    intro i l t z; have hb : m ≤ i+1:=by omega
    have hp:=w.pays i _ _ t z h0 r0; have hv:= piered (h:=h) (A:=A) w.simple w.ratios z w.cap v; obtain ⟨Z,hZ⟩:= attends hv e r u; have he':= (hp.back (V (i+1)) _ Z hv hM (f _ hb z) hZ).1 l
    unfold τ V; rw [pier_step w.simple w.ratios z w.cap v]; apply he'.trans; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ he; simpa only [Credit.products, Credit.lean_cost] using Credit.thickens W (T:=Credit.leanC.prodC E) hx

lemma ferry (F:Frame G h)(E W W':Credit): ∃ D:Credit,∀ Q:SectionData F,∀ A:Levels G,∀ Ñ k u p m c N X M,1≤X→ 0≤ M→∀ e r:ℕ, e≤p→ r≤ k+p→ Chartage Q A Ñ m c N k u p X→∀ P: Era G ℝ,Auth k P→
    (∀ j, m≤ j→j≤c→ Earlier (pier A Ñ N h k c j P) e r u (E.buy X*M)) → (∀ j,m≤ j → j≤ c →∀ i:TagIx F r, ‖row F ((pier A Ñ N h k c j P).2 e r) i‖≤ W.buy X*M) → Fruit 0 1 u (P.2 e r) (W'.buy X*M) → ∀ j,m≤ j→ j≤ c → Fruit 0 1 u ((pier A Ñ N h k c j P).2 e r) (D.buy X*M) :=by
    let D:= Credit.leanC.prodC (E.plus W); refine ⟨W'.plus (Credit.leanC.prodC D),fun Q A Ñ k u p m c N X M hx he e r h0 r0 w P v f g hP j hj pj=>?_⟩; let V j:=pier A Ñ N h k c j P
    let X' i:= W'.buy X*M+ ((c-i:ℕ):ℝ)*(D.buy X*M); have hD:0≤D.buy X*M:= mul_nonneg (zero_le_one.trans (D.purchase hx)) he
    suffices h: ∀ i≤c,m≤ i→ Fruit 0 1 u ((V i).2 e r) (X' i) by
       apply (h j pj hj).more; refine ((add_le_add_right (mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (show c-j≤c-m by omega)).trans w.age) hD) _).trans ?_); rw [←mul_assoc X, ← add_mul]; apply mul_le_mul_of_nonneg_right _ he
       simpa only [Credit.products, Credit.lean_cost] using Credit.fuel W' (Credit.leanC.prodC D) hx
    intro i a; induction a using Nat.decreasingInduction with
    | self=> intro _; simpa only [V,X',pier_top,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero] using hP
    | of_succ i u' ih=>
        intro s; have hs:m≤ i+1:=by omega
        have hb:= ih hs
        unfold V; rw [pier_step w.simple w.ratios u' w.cap v]; let Z:= V (i+1)
        obtain ⟨hp',hf⟩:= (w.pays i _ _ s u' h0 r0).back Z (E.buy X*M) _ (piered w.simple w.ratios u' w.cap v) (mul_nonneg (zero_le_one.trans (E.purchase hx)) he) (f _ hs u') hb
        have H:= hf _ (mul_nonneg (zero_le_one.trans (W.purchase hx)) he) (g _ hs u')
        apply H.more; refine le_trans (add_le_add (mul_le_of_le_one_left hb.C (rollFrac_le ..)) (show X*_≤D.buy X*M from ?_)) (le_of_eq ?_)
        · unfold D; rw [Credit.products, Credit.lean_cost,←add_mul,←mul_assoc X]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Credit.fuel _ _ hx) (zero_le_one.trans hx)) he
        unfold X'; rw [show c-i=c-(i+1)+1 from by omega,Nat.cast_add,Nat.cast_one]; ring
end YM.WilsonCoeffUV.Mer.Xa
