import YM.WilsonCoeffUV.Stable.RefundCanonical
/-! # Inverse PUSH refunds. Age=CourseS concrete. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{V:Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}

lemma barley_bill (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W V:Credit): ∃ C:Credit,∀ R: Canopy H T p v E W V,R.m<R.c →∀ j≤e,∀ i:Alma F,
    let t:=R.R; let P n:=barley t.draws t.paid T p n k R.c; twain (t.cash C R.m*t.tempC R.m R.c*R.wealth) (t.tempC R.c R.b) (coeff j (P R.N R.X R.m i)) (coeff j (P R.M R.Y R.m i)):=by
    obtain ⟨Z,h⟩:= flowering H T p v E W V; let z:= jumped E Z; let P:= buoy H T p v e 0 E W V; let C:= P.prodC z; let X:= C.plus (C.prodC (doubling E)); refine ⟨X,fun R g j w i=>?_⟩; intro L P'
    let B:=(P' R.N R.X R.m); let Y:=(P' R.M R.Y R.m); let S:= { R with m:=R.m+1,ha:=R.ha.trans R.m.le_succ,hv:=g}; have hx:R.m< R.b:= g.trans_le R.ht; have hz:L.anchor≤R.m:=R.ha
    let A:= S.atN; let N:=S.atM; let O:=Spray L.draws L.paid T p R.N R.m k; let F':=coeff j (O N i)
    let s:=L.tempC R.c R.b; have hs:0≤s:= (trail_pos ..).le; let y:=L.y R.m; have hy:1≤y:= L.depth _ hz; let γ:=L.tempC R.m R.c; have hγ:0≤γ:= (trail_pos ..).le; let t:= R.wealth; have ht:0≤t:= R.ex.2.2.1; let M:= z.buy y*γ*t; have hM:0≤M:=mul_nonneg (mul_nonneg (zero_le_one.trans (z.purchase hy)) hγ) ht
    have hp :∀ i≤e,∀ j,YieldP 0 1 u M s (A.2 i j) (N.2 i j):=fun i u j=> (h S i u j).step (mul_le_mul_of_nonneg_right (lift_money L hz Z R.c) ht) hs
    let θ:= L.cash (doubling E) R.m * L.tempC R.m R.b; have hE:0≤ (doubling E).buy y:= zero_le_one.trans (Credit.purchase _ hy); have hθ:0≤θ:= mul_nonneg hE (trail_pos ..).le
    have hr:= brace R.L R.ha hx R.hn R.hm (le_refl e) (Nat.zero_le (k+e)); let Z:=P.buy y
    have ha: twain (Z*M) θ F' (coeff j (Y i)):= (hr M hM N N (fun i j p=> YieldP.same (hp i p j).wane hθ)).2 _ _ w
    have hN: twain (Z*M) θ (coeff j (B i)) (coeff j ((Spray L.draws L.paid T p R.M R.m k A) i)) := (hr M hM A A (fun i j p=> YieldP.same (hp i p j).wax hθ)).2 i _ w
    have hD:‖coeff j (O (A-N) i)‖≤ Z*(M*s):= ((hr _ (mul_nonneg hM hs) (A-N) (A-N) (fun a b w=> YieldP.same (P:=(A-N).2 a b) (hp a w b).toll hθ)).2 i _ w).main
    have hA:=R.ha; have hS:= (trail_pos L.draws.S R.c R.b); have hC:Z*M=C.buy y*γ*t:=by unfold Z M C; rw [Credit.products]; ring
    let Q:= X.buy y*γ*t; have hh:Z*M≤ Q:=by rw [hC]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.thickens _ hy) hγ) ht
    refine ⟨hN.main.trans hh,ha.side.trans hh,?_⟩; have hA:On k A:= (nursing R.L (m:=R.m+1) (R.ha.trans R.m.le_succ) g (R.ht.trans R.hn) R.ex.1 R.ex.2.1).1; have hQ: On k N:= (nursing R.L (m:=R.m+1) (R.ha.trans R.m.le_succ) g (R.ht.trans R.hm) R.ey.1 R.ey.2.1).1
    have heN:= hx.trans_le R.hn
    have he : coeff j (B i)-coeff j (Y i)=coeff j (O (A-N) i)+(F'-coeff j (Y i)):=by
       have he: O (A-N)=O A-O N:= by unfold O Spray; rw [Shed_sub _ _ heN L.hG L.green hA hQ, On.read_sub F (ShedG _ _ heN L.hG L.green hA le_rfl) (ShedG _ _ heN L.hG L.green hQ le_rfl)]
       rw [he,Pi.sub_apply,map_sub]; change _-_ = coeff j (B i)- F'+_; ring
    change ‖coeff j (B i)-coeff j (Y i)‖≤ Q*s; rw [he]; apply (norm_add_le ..).trans ((add_le_add hD ha.gap).trans ?_); have hv: θ≤ (doubling E).buy y * s:=mul_le_mul_of_nonneg_left (PathCost.narrow _ g.le _) hE; apply (add_le_add_right (mul_le_mul_of_nonneg_left hv (mul_nonneg (zero_le_one.trans (Credit.purchase _ hy)) hM)) _).trans
    rw [show Z*(M*s)+ Z*M*((doubling E).buy y*s)= (Z*M* s)+Z*M*((doubling E).buy y*s) from by ring,hC]; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.fuel C (C.prodC (doubling E)) hy) hγ) ht) hs); exact le_of_eq (by rw [Credit.products C (doubling E)]; ring)

-- bundle pivot arbitrary, buy stock from Cohorts
lemma uniformPays {α:Type*}{P:α→Credit→Prop}(s:Finset α)(p:∀ i∈s,∃ X,P i X)(h:∀ i∈s,∀ E W,(∀ y,1≤y→ E.buy y ≤ W.buy y)→ P i E→ P i W): ∃ X:Credit,∀ i∈s,P i X:=by
    classical
    induction s using Finset.induction_on with
    | empty=> exact ⟨Credit.unit,by simp⟩
    | @insert i s e ih=>
       have he:=Finset.mem_insert_self i s; obtain ⟨V,hv⟩:=p i he; obtain ⟨X,hX⟩:= ih (fun i hi=>p i (Finset.mem_insert_of_mem hi)) (fun i hi=> h i (Finset.mem_insert_of_mem hi)); refine ⟨V.plus X, fun b q=>?_⟩; rcases Finset.mem_insert.mp q with x|x; subst b; exact h i he _ _ (fun i v=>Credit.thickens _ v) hv; exact h b q _ _ (fun i v=>Credit.thickened _ v) (hX b x)

-- stronger positional dependency from proofs; not actual graphs plus optional identity channel.
section
variable {T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit}
variable (H T p e E W K)
lemma SeasonM : ∃ C:Credit,∀ (t: CourseS H T p e E W K)(i:ℕ), i≤ e →
    let A:=t.vols; let B n:=bindingS A.draws A.paid T p n t.spur t.length false;
    ∀ j j',twain (C.buy t.Age) t.cab (lineS (B t.I.n) i j j') (lineS (B t.I.N) i j j') :=by
    let P (i:ℕ)(C:Credit): Prop:=∀ (t: CourseS H T p e E W K),let A:=t.vols; let B n:=bindingS A.draws A.paid T p n t.spur t.length false;
                                                   ∀ j j',twain (C.buy t.Age) t.cab (lineS (B t.I.n) i j j') (lineS (B t.I.N) i j j')
    obtain ⟨X,g⟩:= uniformPays (P:=P) (Finset.range (e+1)) (fun i h=>glacier H T p e E W K false _ (Nat.le_of_lt_succ (Finset.mem_range.mp h))) (fun i _ x y ht v=> by intro t U P j j'; exact (v t j j').lift (ht _ t.I.warm) (trail_pos ..).le)
    exact ⟨X,fun t i v=>g _ (Finset.mem_range.mpr (by omega)) t⟩
lemma SeasonC : ∃ V:Credit,∀ (t:CourseS H T p e E W K)(i j:ℕ),i≤ e→j≤e → let A:=t.vols; let B n:= relativeC A.draws A.paid n t.spur t.length; twain (V.buy t.Age) t.cab (coeff i ((B t.I.n)^j)) (coeff i ((B t.I.N)^j)):=by
    let S:= (Finset.range (e+1))×ˢ(Finset.range (e+1)); let P (k:ℕ×ℕ)(C:Credit): Prop:=∀ t:CourseS H T p e E W K, let A:=t.vols; let B n:= relativeC A.draws A.paid n t.spur t.length; twain (C.buy t.Age) t.cab (coeff k.1 ((B t.I.n)^k.2)) (coeff k.1 ((B t.I.N)^k.2))
    have H : ∀ i∈ S,∃ V:Credit,P i V:=by
       rintro ⟨i,j⟩ h; have hx:i < e+1:=Finset.mem_range.mp (Finset.mem_product.mp h).1
       let F (t:WindowS G (e+1) E) (n):= relativeC t.robe.draws t.robe.paid n t.base t.span
       obtain ⟨d,C,h,H⟩:= clipped_pow (WindowS.payments G (e+1) E) (i:=i) (p:=fun t:WindowS G (e+1) E=>F t t.n) (q:=fun t:WindowS G (e+1) E=> F t t.N) j (fun i g=> Bank.descend G (e+1) i E (by omega))
       let V: Credit:= ⟨d,max 1 C,le_max_left ..⟩; refine ⟨V,?_⟩; intro t G J
       have hp :C*t.Age^d≤ V.buy t.Age:= mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans t.I.warm) _)
       have ht:= (H t.I).lift hp (trail_pos ..).le; dsimp only [F,Pi.pow_apply] at ht; rw [t.peace] at ht; exact ht
    obtain ⟨X,f⟩:= uniformPays (P:=P) S (fun i hi=> H i hi) (fun i _ x y v H=> by intro t A B; exact (H t).lift (v _ t.I.warm) (trail_pos ..).le); exact ⟨X,fun t i j v h=>f (i,j) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩) t⟩
end
end YM.WilsonCoeffUV.Shard
