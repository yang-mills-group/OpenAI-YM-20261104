import YM.WilsonCoeffUV.Stable.Budget
/-! # Return and provision. Whole coefficient norm. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}
variable {T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit} {R S: TowerS G D}
lemma Creed_more (H:Hol G)(T:SectionData F)(p:h<D)(e u:ℕ)(E W:Credit) : ∃ C:Credit,∀ (L:Theatre H T p e E W)(m b N M i:ℕ), L.V.anchor ≤ m→m≤ b→ b≤ N→b≤M→i≤e → ∀ x:Alma F,∀ r,YieldP 0 1 u (L.V.cash C m) (L.V.tempC m b) ((L.lore N m).2 x i r) ((L.lore M m).2 x i r):=by
    obtain ⟨X,f⟩:=uniformPays (P:=fun r V=>∀ x:ℝ,1≤x→ (ferris H T p e r u E W).buy x ≤ V.buy x) (Finset.range (h+e+1)) (fun i _=> ⟨_,fun _ _=> le_refl _⟩) (fun r _ x y h p i hi=> (p i hi).trans (h i hi))
    refine ⟨X,fun L m b N M i a z t v' j x r=>?_⟩
    have hp:=L.V.depth _ a; have hz:= (trail_pos L.V.draws.S m b).le
    by_cases he:r≤valence F x+i
    · exact (creed L a z t v' u r x j).step (f _ (Finset.mem_range.mpr (by have hg:= valence_cap F x; omega)) _ hp) hz
    rw [show (L.lore N m).2 x i r=0 from solo_shape ((production L (z.trans t) a).1.scan.solo x) _ _ (by omega),show (L.lore M m).2 x i r=0 from solo_shape ((production L (z.trans v') a).1.scan.solo x) _ _ (by omega)]; exact YieldP.zero.step (zero_le_one.trans (X.purchase hp)) hz
lemma YieldP.diff {u r D:ℕ}{P Q V W: ChamberTen G (Vote D) r}(p:YieldP 0 1 u A δ P Q)(t:YieldP 0 1 u B δ V W): YieldP 0 1 u (A+B) δ (P-V) (Q-W) := by
   refine ⟨p.wax.diff t.wax zero_le_one,p.wane.diff t.wane zero_le_one,?_⟩; rw [sub_sub_sub_comm,add_mul]; exact p.toll.diff t.toll zero_le_one

lemma tenderPV (X Y:Island F D)(e r:ℕ)(A:ℝ){P Q:Verse F}(h:∀ i≤ e,∀ j,twain C δ (coeff i (P j)) (coeff i (Q j)))(v:∀ i≤e,∀ j,YieldP 0 1 u A δ (X.2 j i r) (Y.2 j i r))(hA:0≤A)(hx:0≤C)(hd:0≤δ) (hk:k≤ e): YieldP 0 1 u ((Fintype.card (Alma F)*(e+1:ℕ):ℕ)*2*A*C) δ ((Shrine X P).2 k r) ((Shrine Y Q).2 k r):=by
   apply (tenderOp X Y r (fun i p v=>h p (v.trans hk) i) (fun x j v'=>v j (v'.trans hk) x)).step _ hd
   rw [show (∑ _i:Alma F,∑ _ ∈Finset.antidiagonal k,2*A*C)=(Fintype.card (Alma F):ℝ)*((k+1:ℕ)*(2*A*C)) by simp]
   rw [Nat.cast_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show ((k+1:ℕ):ℝ)≤ (e+1:ℕ) by exact_mod_cast Nat.add_le_add_right hk 1) (by positivity)) (by positivity : 0≤ (Fintype.card (Alma F):ℝ))); exact le_of_eq (by ring)
lemma burdenOn (t:Torch H T p v E W K)(hm:t.L.V.anchor≤m)(v':m+i≤c)(p':c≤N)(P:On k S)(Q:opal F S=0) : On k (burden t.L.V.draws t.L.V.paid T p N k c m i S):=by
    have hz:=hm.trans (Nat.le_add_right m i); exact On.diff ((nursing t hz v' p' P Q).1) (Shrine_on (t.L.lore N (m+i)) (production t.L (v'.trans p') hz).1 _ v.hk)
-- ALL installments, from normalized Y. General rendering below
lemma burden_credit (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K V:Credit): ∃ C:Credit,∀ (t:Chest H T p v E W K V)(i j:ℕ), t.I.m+i≤t.I.c → j≤e→ ∀ r:ℕ,
    let I:=t.I; let L:=I.R; let Q n:=burden L.draws L.paid T p n k I.c I.m i; YieldP 0 1 u (C.buy t.quest.Age * L.tempC (I.m+i) I.c*I.wealth) t.quest.cab ((Q I.N I.X).2 j r) ((Q I.M I.Y).2 j r):=by
    obtain ⟨X,h⟩:= Creed_more H T p e u E W; obtain ⟨Y,q⟩:= flowering H T p v E W K; obtain ⟨U,p'⟩:= bootPaid H T p v E W K V
    let A:ℝ:= (Fintype.card (Alma F)*(e+1:ℕ):ℕ)*2
    let C:=Y.plus (((pur A).prodC X).prodC U); refine ⟨C,?_⟩; intro t i j v' x r I L V'
    rw [t.rateK]; let Z:=(I.m+i); let θ:= L.tempC I.c I.b; let δ:=L.tempC Z I.c; let y:=t.quest.Age; have hy:1≤y:= t.quest.I.warm; have hy':L.anchor≤Z:= I.ha.trans (Nat.le_add_right ..); have hθ:0≤ θ:= (trail_pos ..).le; have hδ:0≤δ:= (trail_pos ..).le; let B:= I.wealth; have hb:0≤B:= I.ex.2.2.1
    let F n:=I.L.L.lore n Z; let T' n:= boot L.draws L.paid T p n k I.c I.m i; let U':= U.buy y*δ*B; have hu:0≤ U':= mul_nonneg (mul_nonneg (zero_le_one.trans (U.purchase hy)) hδ) hb
    have hx:0≤ X.buy y:=zero_le_one.trans (X.purchase hy); have he l (h':l≤ e) i: YieldP 0 1 u (X.buy y) θ ((F I.N).2 i l r) ((F I.M).2 i l r):= ((h I.L.L Z I.b I.N I.M l hy' (v'.trans I.ht) I.hn I.hm h' i r).expand (PathCost.narrow _ v' _)).step (X.elder (L.depth _ hy') (t.water v')) hθ
    let L':={ I with m:=Z,ha:=hy',hv:=v'}; have hX:= q L' j x r
    have hL:= hX.diff (tenderPV (F I.N) (F I.M) e r (X.buy y) (P:=T' I.N I.X) (Q:=T' I.M I.Y) (fun j h=>p' t i v' j h) he hx hu hθ x)
    apply hL.step _ hθ; change Y.buy (L.y Z)*δ*B + A*X.buy y*U' ≤ C.buy y*δ*B; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.fuel Y (((pur A).prodC X).prodC U) hy) hδ) hb); simp only [add_mul, Credit.products]; apply add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Y.elder (L.depth _ hy') (t.water v')) hδ) hb) _; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal A y) hx) hu).trans; exact le_of_eq (by unfold U'; ring)
end YM.WilsonCoeffUV.Shard
