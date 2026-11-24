import YM.OPE.Compatible.Portage.Market
/-! Accounting for uniformly finite polynomial costs, several independent
scales. Positive polylog ratios called Round for comparing inverse costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open scoped Topology BigOperators Classical
variable {I J X Y Z:Type*} {l : Filter I} {f : Filter J}{T q r : I→ℝ} {p p':I→X}{w:I→Y}
def Score [Norm X](l:Filter I)(T:I→ℝ)(p:I→X):Prop:=∃ a,RateLE l (Real.log ∘ T) p a
namespace Score
lemma liftp [Norm X] (h:Score l T p) [Norm Y] (hw : ∀ᶠ i in l, ‖w i‖ ≤ ‖p i‖): Score l T w:=by obtain ⟨a,h⟩:=h; exact ⟨a,h.transfer hw⟩
lemma congr [Norm X] (h:Score l T p)(hp:p=ᶠ[l] p'):Score l T p':= h.imp fun _ hx=> RateLE.congr hx hp
lemma under [Norm X] (h:Score l T r)(hw : ∀ᶠ i in l, ‖p i‖ ≤ r i): Score l T p:= h.liftp (hw.mono fun _ hi=> hi.trans (Real.le_norm_self _))
lemma pointwise (h:Score l T r)(hw : ∀ᶠ i in l, q i ≤ r i)(hp:∀ᶠ i in l,0 ≤ q i):Score l T q:=by apply h.under; filter_upwards [hw,hp] with i hi hp; rwa [Real.norm_of_nonneg hp]
lemma steady [Norm X] (x:X)(hT:Tendsto T l atTop): Score l T (fun _=>x) := ⟨_,RateLE.const x (Real.tendsto_log_atTop.comp hT)⟩
lemma bound [Norm X](A:ℝ)(h:Tendsto T l atTop)(hp:∀ᶠ i in l,‖p i‖≤ A):Score l T p:= ⟨_,RateLE.absBound A (Real.tendsto_log_atTop.comp h) hp⟩
lemma fitsQ [Norm X] (h:Score l T p)(ht:Tendsto T l atTop):∃ a:ℕ,∀ᶠ i in l,‖p i‖≤ T i^a:=by
   obtain ⟨a,hp⟩:=h; obtain ⟨c,hc⟩:= exists_nat_gt a; refine ⟨c,?_⟩; filter_upwards [ht.eventually_gt_atTop 0,hp c hc] with i hi hx; exact hx.trans_eq (by change Real.exp (_*Real.log (T i))=_; rw [Real.exp_nat_mul,Real.exp_log hi])
lemma product [SeminormedRing X] (h:Score l T p)(ht:Score l T p') : Score l T (fun i=>p i*p' i) :=by obtain ⟨a,h⟩:=h; obtain ⟨b,ht⟩:=ht; exact ⟨_,h.mul ht⟩
lemma power [SeminormedRing X] (n:ℕ)(h:Score l T p)(ht:Tendsto T l atTop): Score l T (fun i=>p i^n):=by obtain ⟨a,h⟩:=h; exact ⟨_,h.pow _ (Real.tendsto_log_atTop.comp ht)⟩
lemma dot [NormedField X][NormedAddCommGroup Y][NormedSpace X Y](h:Score l T p)(ht:Score l T w) : Score l T (fun i=>p i • w i):=by obtain ⟨a,h⟩:=h; obtain ⟨c,ht⟩:=ht; exact ⟨_,h.smul ht⟩
lemma plus [SeminormedAddGroup X](h:Score l T p)(hc:Score l T p')(ht:Tendsto T l atTop): Score l T (fun i=>p i + p' i):=by obtain ⟨a,h⟩:=h; obtain ⟨c,hc⟩:=hc; exact ⟨_,h.addMax hc (Real.tendsto_log_atTop.comp ht)⟩
lemma time (h:Tendsto T l atTop): Score l T T:=by
   have he:= RateLE.exp 1 (Real.tendsto_log_atTop.comp h); refine ⟨1,he.congr ?_⟩; filter_upwards [h.eventually_gt_atTop 0] with i hi; simp only [comp_apply,one_mul,Real.exp_log hi]
lemma summar [SeminormedAddCommGroup X](A:Finset Y)(v:Y→I→X)(ht:Tendsto T l atTop)(hQ:∀ i∈A,Score l T (v i)):Score l T (fun i=>∑ x∈A,v x i):=by
    induction A using Finset.induction_on with
    | empty=> simpa using steady (0:X) ht
    | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact Score.plus (hQ i (Finset.mem_insert_self ..)) (ih (fun j hj=>hQ j (Finset.mem_insert_of_mem hj))) ht
lemma multiply [SeminormedCommRing X](A:Finset Y)(v:Y→I→X)(ht:Tendsto T l atTop)(hQ:∀ i∈A,Score l T (v i)):Score l T (fun i=>∏ x∈A,v x i):=by
    induction A using Finset.induction_on with
    | empty=> simpa using steady (1:X) ht
    | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact Score.product (hQ i (Finset.mem_insert_self ..)) (ih (fun j hj=>hQ j (Finset.mem_insert_of_mem hj)))
lemma ceiling (h:Score l T r)(ht:Tendsto T l atTop)(hq:∀ᶠ i in l,0 ≤ r i):Score l T (fun i=>(Nat.ceil (r i):ℝ)):=by
    refine (h.plus (Score.steady (1:ℝ) ht) ht).pointwise (hq.mono fun _ hp=> (Nat.ceil_lt_add_one hp).le) (Eventually.of_forall fun _=> Nat.cast_nonneg _)
lemma maxS (h:Score l T r)(he:Score l T q)(hT:Tendsto T l atTop) : Score l T (fun i=> max (r i) (q i)):=by
    refine Score.under (p:=fun i=> max (r i) (q i)) (r:=fun i=> ‖r i‖+‖q i‖) ((h.liftp (p:=r) (w:=fun i=>‖r i‖) (by simp)).plus (he.liftp (p:=q) (w:=fun i=>‖q i‖) (by simp)) hT) (Eventually.of_forall fun i=>?_); rcases le_total (r i) (q i) with h|h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (norm_nonneg _)
    rw [max_eq_left h]; exact le_add_of_nonneg_right (norm_nonneg _)
lemma relative [Norm X]{u:I→ℝ}(h:Score l u p)(hu:Score l T u)(ht:Tendsto T l atTop)(hq:Tendsto u l atTop): Score l T p:=by obtain ⟨n,h⟩:=Score.fitsQ h hq; exact (hu.power n ht).under h
lemma comp [Norm X] (h:Score l T p){r:J→I}(hp:Tendsto r f l): Score f (T∘r) (p∘r):=h.imp fun _ h=> h.comp hp
lemma shoot [Norm X] (h: Score l T p){r:Filter I}(hp:r≤l): Score r T p:=h.imp fun _ h=>h.shrink hp
end Score
structure Round (l:Filter I)(T r:I→ℝ) :Prop where
    pos : ∀ᶠ i in l,0<r i
    up : Score l T r
    down : Score l T (fun i=>(r i)⁻¹)
namespace Round
variable (h: Round l T r)
include h
lemma inv :Round l T (fun i=>(r i)⁻¹):=⟨h.pos.mono (fun i hi=>inv_pos.mpr hi),h.down,h.up.congr (by simp)⟩
lemma mul (hq:Round l T q): Round l T (fun i=>r i*q i):=⟨(h.pos.and hq.pos).mono (fun _ hp=> mul_pos hp.1 hp.2),h.up.product hq.up,(h.down.product hq.down).congr (by simp [mul_comm])⟩
lemma div (hq:Round l T q):Round l T (fun i=>r i/q i):=by simpa only [div_eq_mul_inv] using h.mul hq.inv
lemma power (k:ℕ)(ht:Tendsto T l atTop): Round l T (fun i=>r i^k):= ⟨h.pos.mono (fun _ hp=>pow_pos hp k), Score.power k h.up ht, by simpa only [inv_pow] using Score.power k h.down ht⟩
lemma adjust (hq:r=ᶠ[l] q):Round l T q:= ⟨(h.pos.and hq).mono fun _ e=> e.2 ▸ e.1, h.up.congr hq,h.down.congr (by filter_upwards [hq] with i h using congr_arg _ h)⟩ -- parsing
lemma sum (hp:Round l T q)(ht:Tendsto T l atTop):Round l T (fun i=>r i+q i):=by
   have he:∀ᶠ i in l,0<r i+q i:= (h.pos.and hp.pos).mono (fun i he=> add_pos he.1 he.2); refine ⟨he,h.up.plus hp.up ht,h.down.pointwise ?_ (he.mono fun i he=>(inv_pos.mpr he).le)⟩
   filter_upwards [h.pos,hp.pos] with i h hq; exact inv_anti₀ h (le_add_of_nonneg_right hq.le)
lemma less (hq:Round l T q)(ht:Tendsto T l atTop):Round l T (fun i=> min (r i) (q i)):=by
    have hp:∀ᶠ i in l, 0< min (r i) (q i):=(h.pos.and hq.pos).mono fun i he=>lt_min he.1 he.2
    refine ⟨hp,h.up.pointwise (Eventually.of_forall fun i=>min_le_left ..) (hp.mono fun i hi=>hi.le),(h.down.maxS hq.down ht).pointwise ?_ (hp.mono fun _ hi=> (inv_pos.mpr hi).le)⟩
    filter_upwards with i; rcases le_total (r i) (q i) with hi|hi; simp only [min_eq_left hi,le_sup_left]; simp only [min_eq_right hi,le_sup_right]
omit h
lemma const {a:ℝ}(ha:0<a)(ht:Tendsto T l atTop): Round l T (fun _=>a):=⟨Eventually.of_forall fun _=>ha,Score.steady _ ht,Score.steady _ ht⟩
lemma multiple (A:Finset X)(v:X→I→ℝ)(ht:Tendsto T l atTop)(h:∀ i∈A,Round l T (v i)):Round l T (fun i=>∏ x∈A,v x i):=by induction A using Finset.induction_on with
    | empty=> simpa using const one_pos ht
    | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact Round.mul (h i (Finset.mem_insert_self ..)) (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
lemma if_inv (hq:∀ᶠ i in l,0<r i)(ht:Score l T r)(hs:Tendsto T l atTop)(hp:∀ᶠ i in l,r i≥1) :Round l T r:= ⟨hq,ht,(Score.steady (1:ℝ) hs).pointwise (hp.mono fun _ hi=> inv_le_one_of_one_le₀ hi) (hq.mono fun _ h=>(inv_pos.mpr h).le)⟩
end Round
end YM.OPE
