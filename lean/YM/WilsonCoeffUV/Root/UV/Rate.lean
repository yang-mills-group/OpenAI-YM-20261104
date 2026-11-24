import YM.WilsonCoeffUV.Root.UV.Tariff
/-! # Full primary graph costs. uniform cutoff tail separated from finite emit. θ. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}
lemma tax_lease (hp:i≤ e)(hk:k≤l+i)(ht:l≤h)(hf:∀ a l' r,oldJobs a l' r i l k  →  Sees H T p e E W U' a l' r)(H':Hanks H T p e E W V' i l k):∃ Q:Credit, Sees H T p e E W Q i l k:=by
   let Z:=blockAge G e E U'; let V:=jump E V'; let v:= portC H F p i k l hk; let C:= (((W.prodC (Z.powC v)).prodC V').prodC (Credit.unit.plus V)).prodC (doubling E); let S:=(V'.plus V').plus C
   refine ⟨V'.plus S.behind,fun L m ha b N M hm hp' hM j hj=>?_⟩
   let R:= L.V; have hy:=R.depth _ ha
   refine ⟨Cork.cost (H' L _ ha N (by omega) j hj) (Credit.thickens _ hy),Cork.cost (H' L _ ha M (by omega) j hj) (Credit.thickens _ hy),?_⟩
   suffices H:∀ i'≤ b,∀ h':L.V.anchor≤ i',∀ j: Alma F,valence F j=l  → Twig 0 (L.angle i' h').lamp.exitS (S.tower Credit.liftA (R.y i')*R.tempC i' b) ((L.lore N i').2 j i k-(L.lore M i').2 j i k) by exact Cork.cost (H m hm ha j hj) (mul_le_mul_of_nonneg_right ((Credit.donation S Credit.liftA Credit.lift_good _ hy).trans (Credit.thickened V' hy)) (trail_pos ..).le)
   intro m hm
   induction hm using Nat.decreasingInduction with
   | self=>
      intro p' j u; rw [Realm.tempC,trail_end,mul_one]; have hv:=R.depth b p'; exact Cork.cost (Cork.sub (H' L b p' N hp' j u) (H' L b p' M hM j u)) (((Credit.fuel _ _ hv).trans (Credit.thickens _ hv)).trans (Credit.raised S Credit.liftA _ Credit.lift_good hv))
   | of_succ i' he ih=>
      intro h' j t
      let I:=L.angle i' h'; let s:=I.lamp.input; let y:=R.y i'; let γ:= arc R.draws.S i'; let z:=R.y (i'+1)
      have hv:1≤ y:= R.depth i' h'; have ht':1≤ z:= L.V.depth _ (show L.V.anchor≤ i'+1 from by omega)
      let d:=R.tempC i' b; let d':=R.tempC (i'+1) b; let δ:= R.cash (doubling E) i'*d
      have hd:= R.also_temp (b:=b) h'
      have hD:0≤δ:= (trail_pos ..).le.trans hd
      let B:= S.tower Credit.liftA z; let A:=V.buy y; let X:=Z.buy y; let K:=V'.buy y
      have hX:= Z.purchase hv; have hK:= V'.purchase hv; have hx : 0≤A:= zero_le_one.trans (V.purchase hv)
      obtain ⟨u,pU,z'⟩:= buoyant L h' hp he hp' hM hf
      have hl : Plinth (L.lore N (i'+1)).2 (L.lore M (i'+1)).2 s i k l A (B*d') := by
         have hh j (h:valence F j=l) N (g:b≤ N): Twig 0 s A ((L.lore N (i'+1)).2 j i k):= Cork.mono (Cork.cost (H' L (i'+1) (by omega) N (by omega) j h) (R.shift_z _ h')) (L.touch i' h')
         exact ⟨fun j h=> hh j h N hp',fun j h=> hh j h M hM,fun j h=> Cork.mono (ih (by omega) j h) (L.touch i' h')⟩
      have hb:0≤ B*d':=(hl.peek j t).1
      apply Cork.cost ((treadmill L h' ht hp hk he hp' hM hX hx hK u pU z' hl (fun j t=> H' L i' h' M (by omega) j t)).peek j t)
      have h₁:skulk H F p l k I/(inkPin I).patch.L.val*(B*d')≤ Real.exp (-γ/4)*B*d:= by apply (mul_le_mul_of_nonneg_right (archFoam L h' ht (by omega)) hb).trans_eq; rw [show d=Real.exp (-γ/4)*d' from one_leg .., show -PathCost.arc _ _ /2= -γ/4+ -γ/4 by unfold γ; ring, Real.exp_add]; ring
      have hQ: 0≤ 1+A:=by positivity
      have h₂ : hills H F p i k l hk I * X^v * K*(1+A)*δ≤S.buy y*d:=by
          refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((L.spend i' h').story i _ _ hp ht hk) (pow_nonneg (zero_le_one.trans hX) _)) (zero_le_one.trans hK)) hQ) hD).trans ?_
          apply le_trans _ (mul_le_mul_of_nonneg_right (Credit.thickened _ (V:=C) hv) (show 0≤d from (trail_pos ..).le)); unfold C; simp only [Credit.products,Credit.power]; unfold δ; rw [← mul_assoc]; have hp:= Credit.fuel Credit.unit V hv; rw [Credit.unit_cost] at hp; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg (zero_le_one.trans (W.purchase hv)) (pow_nonneg (zero_le_one.trans hX) _)) (zero_le_one.trans hK))) (zero_le_one.trans ((doubling E).purchase hv))) (trail_pos ..).le
      refine (add_le_add h₁ h₂).trans ?_; rw [← add_mul]; exact mul_le_mul_of_nonneg_right (Credit.step_cap _ hv ht' (R.age i' (i'+1) h' (by omega)) (arch_pos ..)) (trail_pos ..).le
lemma vacant_columns (g:h<l ∨ l+i<k): Sees H T p e E W V' i l k:= by
    intro L m h b N M p hn hm j v
    have he:= valence_cap F j
    rw [show (L.lore N m).2 j i k=0 from solo_shape ((production L (show m≤ N from by omega) h).1.scan.solo j) i k (by omega), show (L.lore M m).2 j i k=0 from solo_shape ((production L (show m≤ M from by omega) h).1.scan.solo j) i k (by omega)]; exact Shelf.zero.step (zero_le_one.trans (V'.purchase (L.V.depth m h))) (trail_pos ..).le
-- lex recursion on bounded index. collect via triangle wave.
lemma plenitude (hp:i≤e)(hk:l≤h)(ht:∀ a b c,a< i ∨ a=i ∧  b<l  →  Sees H T p e E W U' a b c): ∃ V:Credit,(∀ k,Sees H T p e E W V i l k) ∧(∀ y:ℝ,1≤y  →  U'.buy y≤ V.buy y):=by
    suffices hh:∀ k ≤ l+i+1,∃ V:Credit,(∀ j, k≤ j  →  Sees H T p e E W V i l j) ∧ (∀ y:ℝ,1≤ y  →  U'.buy y≤ V.buy y) from (by obtain ⟨V,hv,q⟩:= hh 0 (by omega); exact ⟨V,fun j=>hv j (by omega),q⟩)
    intro k hv
    induction hv using Nat.decreasingInduction with
    | self=> exact ⟨U',fun j h' =>vacant_columns (by omega),fun _ _=> le_rfl⟩
    | of_succ j pp ih =>
       obtain ⟨V,u,v⟩:= ih
       have hh a b c (h:oldJobs a b c i l j): Sees H T (D:=D) p e E W V a b c:= by
          unfold oldJobs at h; by_cases g:a< i ∨ a=i ∧ b<l; · exact (ht a b c g).more v
          have he: b=l:= by omega
          have ha:a=i:=by omega
          rw [he,ha]; exact u c (by omega)
       obtain ⟨C,hC⟩:= Season hp (show j ≤ l+i from by omega) hk hh; obtain ⟨T,hT⟩:= tax_lease hp (show j≤ l+i from by omega) hk hh hC; refine ⟨V.plus T,fun q h=>?_,fun y w=>(v y w).trans (Credit.thickens _ w)⟩; by_cases b:j=q; · subst j; exact hT.more fun _ hb=> Credit.thickened _ hb
       exact (u q (by omega)).more fun _ hb=>Credit.thickens _ hb
lemma width_col (hp:i≤e)(ht:∀ a b c,a< i  →  Sees H T p e E W U' a b c): ∃ V:Credit, (∀ l k, Sees H T p e E W V i l k) ∧(∀ y:ℝ,1≤ y  →  U'.buy y≤ V.buy y):=by
    suffices hh:∀ l≤ h+1,∃ V:Credit,(∀ l' k,l'<l  →  Sees H T p e E W V i l' k) ∧(∀ y:ℝ,1≤ y  →  U'.buy y≤ V.buy y) from (by obtain ⟨V,hv,q⟩:= hh _ le_rfl; refine ⟨V,fun i k=>?_,q⟩; by_cases g:i<h+1; exact hv _ _ g; exact vacant_columns (by omega))
    intro l hv
    induction l with
    | zero=> exact ⟨U',fun i j h=>by omega,fun _ _=>le_rfl⟩
    | succ l ih=>
       obtain ⟨V,b,u⟩:= ih (by omega); obtain ⟨C,g,z⟩:= plenitude hp (show l≤h from by omega) (fun a c k p=>by
          rcases p with h'|⟨h,v⟩; exact (ht a c k h').more u; subst a; exact b _ _ v)
       refine ⟨C,fun l' k u=>?_,fun v hv=>(u v hv).trans (z v hv)⟩
       by_cases h:l'=l; · subst l'; exact g _
       exact (b _ _ (by omega)).more z
-- main
lemma allPlays (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W:Credit): ∃ V:Credit, ∀ i l k,i≤e  →  Sees H T p e E W V i l k:=by
    suffices hh:∀ i ≤e+1,∃V:Credit,∀ j l k,j< i  →  Sees H T p e E W V j l k from (by obtain ⟨V,u⟩:= hh _ le_rfl; exact ⟨V,fun i l k h=>u i l k (by omega)⟩)
    intro i hi
    induction i with
    | zero => exact ⟨E,fun j l k h=>by omega⟩
    | succ i ih=>
       obtain ⟨C,h⟩:= ih (by omega); obtain ⟨U,p,q⟩:= width_col (show i≤e from by omega) h
       refine ⟨U,fun j l k g=>?_⟩; by_cases v:j=i; · subst j; exact p l k
       exact (h j l k (by omega)).more q
end YM.WilsonCoeffUV.Cosmos
