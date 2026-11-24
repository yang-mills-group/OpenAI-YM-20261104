import YM.OPE.Compatible.Lintel.Marble
/-! # Every polynomial winding pain. Accounts at deck norm ∞. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J X Y Z:Type}{G:Gauge}{n m c f:Side} {r d:ℕ}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
-- input Camp at one hop. Winds relative p drawing ∀n. use narrative repeated read only; true comparison consumes. pol error for hectare
section
variable [Fintype I][Fintype J]
omit [Fintype I] in
abbrev folk (p:Script I r):Prop:= ∀ i:ℕ,∃ c,soot i p c
omit [Fintype I] in
lemma folk_whole {p:Script I r}(h:folk p):Summable p:=sootS (h 0).choose_spec
omit [Fintype I] in
lemma folk_pad (A:Row I I)(ha:Whole A)(p:Script I (r+2))(h:folk p):folk (pad A p):=by
    obtain ⟨s,U,hs,H⟩:=ha; exact fun i=>⟨_,pad_charge (strip_mono H le_rfl (le_max_left ..)) hs.le (le_max_right U 0) (h i).choose_spec⟩
omit [Fintype I] in
lemma folk_cot {A:Row I I}(hx:Whole A){P:Script I (r+1)}{Q:Script I (d+1)}(h:folk P)(he:folk Q):folk (cotton A P Q):=by obtain ⟨s,c,hc,H⟩:=hx; exact fun i=>⟨_,cotton_cost (strip_mono H le_rfl (le_max_left c 0)) hc (le_max_right ..) (h i).choose_spec (he i).choose_spec⟩
omit [Fintype I] in
lemma folkS {p:Script I r}(h:folk p)(u:ℝ):folk (u • p):= fun i=>⟨_,Sack.scale_line (h i).choose_spec _⟩
omit [Fintype I] in
lemma folkF {p q:Script I r}(h:folk p)(hp:folk q):folk (p+q):=fun i=> ⟨_, Sack.splits (h i).choose_spec (hp i).choose_spec (fun x=>zero_le_one.trans (payer i x))⟩
omit [Fintype I] in
lemma folkD {p q:Script I r}(h:folk p)(hp:folk q):folk (p-q):=fun i=>⟨_,Sack.subsumes (h i).choose_spec (hp i).choose_spec (fun x=> zero_le_one.trans (payer i x))⟩
omit [Fintype I] in
lemma folkT {A:Row I J}(h:Whole A){p:Script I r}(he:folk p):folk (raft A p):= fun i=> raftBills A h p i (he i).choose_spec
def tuneH (A:Row J J)(P:Script (I⊕J) 3) (Q:Script (I⊕J) 4) (n:Side)(x:Fin 2→deck (I⊕J) n):=
    let T:= ROOT A
    (1/2:ℝ)*(- cityTap (T.acts n) (cotton T P P) x+cityTap (T.acts n) Q x-cityTap (T.acts n) (swing (Equiv.swap (1:Fin 4) 2) (cotton T P P)) x)
def tuneV (A:Row J J)(P: Script (I⊕J) 3)(Q:Script (I⊕J) 4): Script (I⊕J) 2:= let T:=ROOT A; (1/2:ℝ) • (((-1:ℝ) • pad T (cotton T P P) + pad T Q)+(-1:ℝ) • pad T (swing (Equiv.swap (1:Fin 4) 2) (cotton T P P)))
omit [Fintype I] [Fintype J] in
lemma folks_coll {A:Row J J}{P:Script (I⊕J) 3}(hx:Whole A)(h:folk P):folk (swing (Equiv.swap (1:Fin 4) 2) (cotton (ROOT A) P P)):= fun i=> ⟨_, swing_fee ((folk_cot (root_cash A hx) h h) i).choose_spec _⟩
omit [Fintype I] [Fintype J] in
lemma folksT {A:Row J J}{P:Script (I⊕J) 3}{Q:Script (I⊕J) 4}(hx:Whole A)(h:folk P)(he:folk Q):folk (tuneV A P Q):=by
    have ht:Whole (ROOT (I:=I) A):=root_cash A hx; exact folkS (folkF (folkF (folkS (folk_pad _ ht _ (folk_cot ht h h)) _) (folk_pad _ ht _ he)) (folkS (folk_pad _ ht _ (folks_coll hx h)) _)) _
abbrev treasury (A:Script I r)(p: ∀ n:Side,(Fin r→deck I n) →ℝ)(n:ℕ):Prop:=∃ c:ℝ,0 ≤ c∧∀ i x, (i.val:ℝ)^n*‖p i x - library i A x‖ ≤ c * ∏ j,‖x j‖
lemma pad_rapid (A:Row I I)(h:Whole A)(p:Script I (r+2))(hp:folk p)(n:ℕ): treasury (pad A p) (fun i=>cityTap (A.acts i) p) n:=by
    obtain ⟨s,U,h,H⟩:= h; obtain ⟨D,hp⟩:= hp (4+n); let K:=max U 0; let v:ℝ:=(8:ℝ)^(4+n)*widthCost s (4+n)*K*D; have hv:0 ≤ v:=by have hx:= show 0 ≤ D from (tsum_nonneg hp.1).trans hp.2.2; have hy:0≤ widthCost s (4+n):= zero_le_one.trans (widthCost_ge h _); have hz:0≤K:= le_max_right ..; unfold v; positivity
    refine ⟨v,hv,fun i w=>?_⟩; let l:ℝ:= i.val; have hl:0<l:=Nat.cast_pos.mpr i.pos; have he(a:Site i): l^n*‖routeTap (A.acts i) p w a-scribe a (pad A p) w‖≤ (v*(∏ j,‖w j‖))/(l^4):=by
        rw [le_div_iff₀ (pow_pos hl 4), show l^n * _*l^4=l^(4+n)*‖routeTap (A.acts i) p w a-scribe a (pad A p) w‖ by ring]; refine (pad_layers A (strip_mono H le_rfl (le_max_left ..)) h (le_max_right U 0) p D hp i w a).trans_eq ?_; unfold v; ring
    change _*‖cityTap (A.acts i) p w-library i _ w‖≤ _; rw [cellarT,library,← sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg hl.le n)).trans; rw [mul_sum]; apply (sum_le_sum (fun a _=>he a)).trans_eq; rw [sum_const,card_univ,Lattice.site_card,nsmul_eq_mul]; push_cast; exact mul_div_cancel₀ _ (pow_pos hl 4).ne' -- orientation?
lemma treasuryS {P:Script I r}{p:∀ n:Side,(Fin r→deck I n)→ℝ}(h:treasury P p d)(u:ℝ): treasury (u • P) (fun n x=>u*p n x) d:=by
    obtain ⟨c,hc,H⟩:=h; exact ⟨‖u‖*c,by positivity,fun i x=>by rw [libScale,← mul_sub,norm_mul,mul_assoc, mul_left_comm]; exact mul_le_mul_of_nonneg_left (H i x) (norm_nonneg _)⟩
lemma treasuryA {P Q:Script I r}{p q:∀ n:Side,(Fin r→deck I n)→ℝ}(h:treasury P p d)(ha:Summable P)(hx:treasury Q q d)(hb: Summable Q): treasury (P+Q) (fun n x=>p n x+ q n x) d:=by
    obtain ⟨c,hc,H⟩:= h; obtain ⟨b,he,hq⟩:=hx; refine ⟨c+b,add_nonneg hc he, fun i x=>?_⟩; rw [libAdd _ _ ha hb]; rw [show p i x+ q i x-_= p i x-library i P x+(q i x-library i Q x) by ring]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)).trans; rw [mul_add,add_mul]; exact add_le_add (H i x) (hq i x)
lemma tunes_advance (A:Row J J)(h:Whole A)(P: Script (I⊕J) 3)(Q:Script (I⊕J) 4)(hp: folk P)(hq:folk Q)(k:ℕ): treasury (tuneV A P Q) (tuneH A P Q) k:=by
    let T:=(ROOT (I:=I) A); have ht:Whole T:=root_cash A h; let V:= cotton T P P; have hx:folk V:=folk_cot ht hp hp; let D:= swing (Equiv.swap (1:Fin 4) 2) V; have hv:folk D:=folks_coll h hp; let U:= pad T Q; let B:= (-1:ℝ) • pad T V; have hB:folk B:= folkS (folk_pad _ ht V hx) _; have hU:folk U:=folk_pad _ ht _ hq; let C:=(-1:ℝ) • pad T D; have hC:folk C:= folkS (folk_pad _ ht D hv) _; have H:= treasuryA (treasuryS (pad_rapid T ht V hx k) (-1)) (folk_whole hB) (pad_rapid T ht Q hq k) (folk_whole hU); have H:=treasuryA H (folk_whole (folkF hB hU)) (treasuryS (pad_rapid T ht D hv k) (-1)) (folk_whole hC); unfold tuneV tuneH; convert! treasuryS H (1/2) using 1; funext i x; unfold D V T; dsimp only; ring
end
end Script
end YM.OPE.Flume
