import YM.WilsonCoeffUV.Marked.Bounds.Cluster
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric
open scoped Topology BigOperators
variable {c f:Side}{ι α U β V t:Type}{J K I S T:Finset ι}{p:ι→U}{d:Bank.Distance U}{D k:ι→ℕ}{i j e r h N n m l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}

lemma tie_non [Fintype α](p:0<σ):0≤tiePay α i σ:=by cases i with | zero=>rw [tiePay,pow_zero]; exact zero_le_one | succ i=> exact pow_nonneg (boardPay_nn (div_pos p (by positivity))) _

structure ZL (D:ι→ℕ)(S:Finset ι)(e:ℕ) (I:Gear G) where
    L : Rally (e+1) 0 I
    K : family G D
    places : ι→Cover
    token : ι→Site I.patch.L
    β :ℝ
    ht : 0≤β
    hush: K ∅=0
    live S' : S'⊆ S→ ∀ i≤e,∀ j,Wig Bank.terrain (fun i=> I.patch.L.val • places i+lift (token i)) I.past (β^S'.card) S' ((K S').2 i j)
variable {W:Gear G}[DecidableEq ι]
namespace ZL
abbrev quietT (t:ZL D S e W):= Humour W.patch W.kernel W.angle t.L.P.R t.L.P.Q t.L.P.page t.K
lemma silent (t:ZL D S e W) (i j): quietT t ∅ i j=0:=by
    let A:= t.L.P.payMat
    induction i using Nat.strong_induction_on generalizing j with
    | h i ih => cases i with
      | zero=> unfold quietT Humour; rw [Temple]; unfold slidesJ; rw [t.hush]; funext r x; unfold Bank.prism; rw [climb_cut]; simp [tiles,bend,turnTen]
      | succ i=>
          have hx u: Soil.paintC u t.L.P.rays (quietT t ∅) i j=0:=by
              unfold Soil.paintC; refine Finset.sum_eq_zero fun a ha=>?_ ; have h:= Finset.mem_antidiagonal.mp ha; apply Finset.sum_eq_zero; intro b _; rw [ih a.2 (by omega)]; funext r; apply Finset.sum_eq_zero; rintro ⟨p,q⟩ hp; have hs:p+q=r:=Finset.mem_antidiagonal.mp hp; subst r; funext x; unfold ruins swivel; simp [Pi.smul_apply,rill_spell]
          have hy: SubC A (quietT t) i j ∅=0:=by
              simp only [SubC,Finset.powerset_empty,Finset.sum_singleton,Finset.Subset.refl,↓reduceDIte]; unfold Sewing; refine Finset.sum_eq_zero fun a ha=>?_ ; have h:=Finset.mem_antidiagonal.mp ha; apply Finset.sum_eq_zero; intro b _; rw [ih a.1 (by omega)]; funext r; apply Finset.sum_eq_zero; rintro ⟨p,q⟩ hp; have hs:p+q=r:=Finset.mem_antidiagonal.mp hp; subst r; funext x; unfold ruins swivel; simp [Pi.smul_apply,lakeV]
          have hR : rime A (0:Gen (Pen D ∅) (Cloth (Helms W)))=0:=by funext r x; unfold rime ruins; simp [rain_spell]
          unfold quietT Humour; rw [warmUp]; change _ • Sat A t.L.P.rays (quietT t) i j ∅=_; rw [Sat,hx,hx,hy,ih i i.lt_succ_self,hR]; simp
end ZL

def QuestB (σ:Gear G→ℝ)(Q:(I:Gear G)→ZL D S e I→ Ten V (Cloth (Helms I)) i)[NormedAddCommGroup V] (J:Finset ι): Prop:= ∃ d:ℕ, ∀ I:Gear G, ∃ C:ℝ,0≤C∧∀ t : ZL D S e I,Wig Bank.terrain t.places (σ I) (C*t.L.x^d*t.β^J.card) J (Q I t)
variable {w s:Gear G→ℝ}{F F':(I:Gear G)→ ZL D S e I→ Ten V (Cloth (Helms I)) i} [NormedAddCommGroup V]
omit [DecidableEq ι] in
lemma QuestB.plus (p: QuestB w F J)(q:QuestB w F' J): QuestB w (fun I t=> F I t+F' I t) J:=by
    obtain ⟨d,h⟩:=p; obtain ⟨a,p⟩:=q; refine ⟨d+a,fun I=>?_⟩; obtain ⟨A,hA,h⟩:=h I; obtain ⟨B,hB,p⟩:=p I; refine ⟨A+B,add_nonneg hA hB,fun t=>?_⟩; apply ((h t).plus (p t)).more; rw [←add_mul,add_mul A]; exact mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ t.L.rich (by omega)) hA) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ t.L.rich (by omega)) hB)) (pow_nonneg t.ht _)
omit [DecidableEq ι] in
lemma QuestB.zero : QuestB w (fun (I:Gear G) (_:ZL D S e I)=> (0:Ten V (Cloth (Helms I)) i)) J:=⟨0,fun _=>⟨0,le_rfl,fun _=>by rw [zero_mul,zero_mul]; exact Wig.zero⟩⟩
omit [DecidableEq ι] in
lemma QuestB.sum {K:Finset α}{P: (I:Gear G)→ZL D S e I→α→Ten V (Cloth (Helms I)) i}(p:∀ i∈K,QuestB w (fun I t=>P I t i) J):QuestB w (fun I t=> ∑ i∈K,P I t i) J:=by
    classical
    induction K using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact QuestB.zero
    | @insert i K h ih=> simp_rw [Finset.sum_insert h]; exact (p i (Finset.mem_insert_self ..)).plus (ih fun i hi=>p _ (Finset.mem_insert_of_mem hi))
omit [DecidableEq ι] in
lemma QuestB.μ [NormedSpace ℝ V](p: QuestB w F J)(c:ℝ):QuestB w (fun I t=> c • F I t) J:=by
    obtain ⟨d,h⟩:=p; refine ⟨d,fun I=>?_⟩; obtain ⟨A,hA,h⟩:= h I; refine ⟨‖c‖*A,by positivity,fun t=>?_⟩; exact ((h t).μ c).more (le_of_eq (by ring))

omit [DecidableEq ι] in
lemma tuneBr {Z:(I:Gear G)→ ZL D S e I→ Gen (Pen D J) (Cloth (Helms I))}(x:J.Nonempty)(hp:∀ I,0≤w I)(h:∀ I,w I<s I)(f:∀ I,s I≤I.s)(q:QuestB s (fun I t=> Z I t (i+2)) J): QuestB w (fun I t=> rime t.L.P.payMat (Z I t) i) J:=by
    obtain ⟨a,v⟩:=q; refine ⟨a,fun I=>?_⟩; obtain ⟨c,hc,H⟩:=v I
    set D':= sealM i (i+1); let T:= tiePay (Helms I) 2 (s I-w I)
    have ht:0≤ T:=tie_non (sub_pos.mpr (h I)); have hv:= zero_le_one.trans I.bill_nn; have hd:0≤ D':=by unfold D' sealM; positivity
    refine ⟨I.D*c* D'*T,by positivity,fun t=>?_⟩; apply (Wrest (grassyRain (P:= Z I t) ((pm_rate t.L).oneP.mono (f I)) (H t) ((hp I).trans (h I).le)) (h I) (hp I) x).more; apply le_of_eq; unfold T Helms D'; ring
end YM.WilsonCoeffUV.Wheel.Mark
