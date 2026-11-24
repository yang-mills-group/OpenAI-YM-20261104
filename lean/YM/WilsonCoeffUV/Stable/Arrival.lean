import YM.WilsonCoeffUV.Stable.AllHeights
/-!
# Operator-rate pairing across length. Archives output feed important for local stencils.
`v` explicitly lived by strengthened sectors, not matching pre-comp tasks.
-/
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}
variable {H:Hol G}{T:SectionData F}{p:h<D} {v:Rails h k u e}{E W K V V':Credit} {Y X Z:TowerS G D}

def CloudBurst (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K V:Credit)(i r:ℕ):Prop:=∀ L:Torch H T p v E W K,let t:=L.L.V
     ∀ m c b N M, t.anchor≤ m → m≤c → c≤b → b≤N → b≤ M → ∀ X Y:TowerS G D,∀ A,Granite F k u e A X → Granite F k u e A Y →
       (∀ i≤ e,∀ j,Fruit 0 1 u (X.2 i j-Y.2 i j) (A*t.tempC c b)) → Fruit 0 1 u ((breaths t.draws t.paid T p N k c m X).2 i r-(breaths t.draws t.paid T p M k c m Y).2 i r) (t.cash V m*t.tempC m c*(A*t.tempC c b))
lemma CloudBurst.more (q:CloudBurst H T p v E W K V i r)(h:∀ y:ℝ,1≤y → V.buy y≤ V'.buy y): CloudBurst H T p v E W K V' i r:=by
    intro L R m c b N M ha hc p hn hm X Y A hv hu hy; exact (q L m c b N M ha hc p hn hm X Y A hv hu hy).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h _ (R.depth _ ha)) (trail_pos ..).le) (mul_nonneg hv.2.2.1 (trail_pos ..).le))
lemma overBurst (q:k+i< r):CloudBurst H T p v E W K V i r:=by
    intro L R m c b N M ha hc p hn hm X Y A hv hu hy
    rw [solo_shape (nursing L ha hc (p.trans hn) hv.1 hv.2.1).1 _ _ q,solo_shape (nursing L ha hc (p.trans hm) hu.1 hu.2.1).1 _ _ q,sub_zero]; exact Fruit.zero.more (mul_nonneg (mul_nonneg (zero_le_one.trans (V.purchase (R.depth _ ha))) (trail_pos ..).le) (mul_nonneg hv.2.2.1 (trail_pos ..).le))
lemma RainBurst(hh:i≤e)(h': r≤k+i)(t:∀ i' j,lowerGrade i' j i r→ CloudBurst H T p v E W K V i' j):∃ X:Credit,CloudBurst H T p v E W K X i r:=by
    obtain ⟨U,hU⟩:= bloom_all H T p v E W K; have hz : r≤ k+e:= by omega
    let J:=buoy H T p v i r E W K; let S:= (rocket H T p v i r hz E W K).prodC (jumped E V); let C:=S.plus ((J.prodC (jumped E U)).prodC (doubling E)); refine ⟨C.behind,?_⟩
    intro L R m c b N M ha hc hb hn hm X Y A hp hq hw; have hx:= R.depth _ ha; let t':=R.tempC c b; let O:=A*t'
    let P m:=breaths R.draws R.paid T p N k c m X; let Q m:=breaths R.draws R.paid T p M k c m Y; have hA:=hp.2.2.1; have hO:0≤ O:= mul_nonneg hA (trail_pos ..).le
    suffices H':∀ m≤ c,R.anchor≤m → Fruit 0 1 u ((P m).2 i r-(Q m).2 i r) (C.tower Credit.liftA (R.y m)*R.tempC m c*O) by exact (H' _ hc ha).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.donation C _ Credit.lift_good _ hx) (trail_pos ..).le) hO)
    intro m ht; induction ht using Nat.decreasingInduction with
    | self=> intro h; unfold P Q; rw [breath_top,breath_top]; exact (hw i hh r).more (purchase_border C R h hO)
    | of_succ m hy ih=>
        intro h
        let x:=P (m+1); let y:=Q (m+1); let y':=R.y m; have hg:R.anchor ≤ m+1:= h.trans m.le_succ; let U':= jumped E U; let V':= jumped E V; let Z:=V'.buy y'; let K':= U'.buy y'; let γ:= R.tempC m c; have he:1≤ y':=R.depth _ h
        obtain ⟨hP,heP⟩:= nursing L hg hy (hb.trans hn) hp.1 hp.2.1; obtain ⟨hQ,heQ⟩:= nursing L hg hy (hb.trans hm) hq.1 hq.2.1
        have h₀: On k (x-y):= On.diff hP hQ
        have h₁: opal F (x-y)=0:=by rw [On.read_sub F hP hQ, heP,heQ,sub_zero]
        let d:= R.cash (doubling E) m*R.tempC m b; have hκ:0≤ R.cash (doubling E) m:= zero_le_one.trans (Credit.purchase _ he); have hd:0 ≤ d:=mul_nonneg hκ (trail_pos ..).le; have hγ:0≤ γ:= (trail_pos ..).le
        let x':= C.tower Credit.liftA (R.y (m+1))*R.tempC (m+1) c*O; let B:=Z*γ*O; have hx:0≤ B:= mul_nonneg (mul_nonneg (zero_le_one.trans (V'.purchase he)) hγ) hO
        let F n:= Sink R.draws R.paid T p n m k
        have hB j r' (p:lowerGrade j r' i r) : Fruit 0 1 u ((x-y).2 j r') B:= (t j r' p L (m+1) c b N M hg hy hb hn hm X Y A hp hq hw).more (mul_le_mul_of_nonneg_right (lift_money R h V c) hO)
        have hv' :=boat L h (hy.trans_le (hb.trans hn)) hh hz (x-y) h₀ h₁ x' B (ih hg) hx hB
        let V'':= K'*γ*A; have hV:0≤ V'':=mul_nonneg (mul_nonneg (zero_le_one.trans (U'.purchase he)) hγ) hA
        have hk:∀ j r',j≤ i→ YieldP 0 1 u V'' d (y.2 j r') (y.2 j r'):=fun j r' p=> YieldP.same ((hU j (p.trans hh) r' L _ c M hg hy (hb.trans hm) Y A hq).more (mul_le_mul_of_nonneg_right (lift_money R h U c) hA)) hd
        have ht:= (brace L h (hy.trans_le hb) hn hm hh hz V'' hV y y hk).1
        rw [show P m=F N x from breath_step _ _ T p X hy,show Q m= F M y from breath_step _ _ T p Y hy]
        have heq : (F N x).2 i r-(F M y).2 i r=(F N (x-y)).2 i r+((F N y).2 i r - (F M y).2 i r):=by rw [show F N (x-y)=F N x-F N y from Sin_diff R.hG R.green (hy.trans_le (hb.trans hn)) hP hQ]; simp only [Prod.snd_sub,Pi.sub_apply]; abel
        rw [heq]; apply (Fruit.plus hv' ht.toll zero_le_one).more
        refine le_trans ?_ (aging C R h c O hO); rw [add_assoc]; apply add_le_add_right; change _+((J.buy y'*V'')*d) ≤ C.buy y'*γ*O
        have hf: R.tempC m b ≤ t':= PathCost.narrow _ hy.le b
        refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hκ) (mul_nonneg (zero_le_one.trans (J.purchase he)) hV)) _) ?_
        apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.fuel S ((J.prodC U').prodC (doubling E)) he) hγ) hO)
        unfold B V'' S O; simp only [Credit.products]; unfold Z V' K' U'; exact le_of_eq (by unfold cash; dsimp only [y',R]; ring)
lemma cloudPayoff (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K:Credit): ∃ X:Credit,∀ i≤e,∀ j, CloudBurst H T p v E W K X i j:=by
    refine seasonsPaid (fun i j V=>CloudBurst H T p v E W K V i j) k e ?_ (fun i j v _=>overBurst v) (fun i j A B t p=> p.more t)
    intro i hv r V hf; by_cases h:r≤k+i
    · exact RainBurst hv h hf
    exact ⟨V,overBurst (by omega)⟩

structure Canopy (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K:Credit) where
   L : Torch H T p v E W K
   m:ℕ
   c:ℕ
   b:ℕ
   N:ℕ
   M:ℕ
   X : TowerS G D
   Y : TowerS G D
   wealth :ℝ
   ha:L.L.V.anchor≤m
   hv:m≤c
   ht:c≤b
   hn:b≤N
   hm:b≤M
   ex : Granite F k u e wealth X
   ey : Granite F k u e wealth Y
   rate i j:i≤ e → Fruit 0 1 u (X.2 i j-Y.2 i j) (wealth*L.L.V.tempC c b)

variable (c':Canopy H T p v E W K)
namespace Canopy
abbrev R:= c'.L.L.V
abbrev atN:= breaths c'.R.draws c'.R.paid T p c'.N k c'.c c'.m c'.X
abbrev atM:= breaths c'.R.draws c'.R.paid T p c'.M k c'.c c'.m c'.Y
end Canopy

-- accuracy combined native
omit c' in
theorem flowering (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K:Credit): ∃ D:Credit,∀ c':Canopy H T p v E W K,∀ i≤e,∀ j,YieldP 0 1 u (c'.R.cash D c'.m*c'.R.tempC c'.m c'.c*c'.wealth) (c'.R.tempC c'.c c'.b) (c'.atN.2 i j) (c'.atM.2 i j):=by
    obtain ⟨A,h⟩:= bloom_all H T p v E W K; obtain ⟨V,x⟩:=cloudPayoff H T p v E W K; refine ⟨A.plus V,fun t i e j=>?_⟩
    refine ⟨((h i e j).more (fun _ k=>Credit.thickens V k)) t.L t.m t.c t.N t.ha t.hv (t.ht.trans t.hn) t.X t.wealth t.ex, (OrePeak.more (h i e j) (fun _ k=>Credit.thickens V k)) t.L t.m t.c t.M t.ha t.hv (t.ht.trans t.hm) t.Y t.wealth t.ey,?_⟩
    rw [mul_assoc _ t.wealth]; exact ((x i e j).more (fun _ k=>Credit.thickened A k)) t.L t.m t.c t.b t.N t.M t.ha t.hv t.ht t.hn t.hm t.X t.Y t.wealth t.ex t.ey (fun i u j=> t.rate i j u)
end YM.WilsonCoeffUV.Shard
