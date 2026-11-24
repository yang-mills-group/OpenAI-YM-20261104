import YM.WilsonCoeffUV.Stable.Prance
/-! # Ward cost promotes actual ordinary difference replacing mean row, polynomial norm -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Wilson Tree Power PowerSeries Exterior Soil Precision Embroider Fountain Cosmos
open scoped Topology BigOperators
variable {L:Side}{U α V W ι : Type*}{i e k r u j l D:ℕ} {A B C s σ η δ : ℝ} {o:Cover}{G:Gauge}
def vealS (G:Gauge)(a b:G.Color)(j:G.ColorIndex)(k r:ℕ):ℝ:= ((Fintype.card (Fin k→ Hooks G):ℝ)* ∑ i, ‖rye (electric a b j) k i‖)*(r-k+1:ℕ)
def courseWind (a:G.Color)(k u r:ℕ) :ℝ:= ∑ _:Axis, ∑ i:G.ColorIndex,(vealS G a 0 i k r+2^u*vealS G 0 a i k r)
def zenithW (G:Gauge)(e u r:ℕ) : ℝ:= ∑ i:G.ColorIndex, ((r+1:ℕ):ℝ)⁻¹* ∑ j∈(Finset.antidiagonal e).erase (0,e), courseWind (coatC G (Pi.single i 1)) j.1 u r
lemma costW_nn (G:Gauge)(e u r:ℕ):0≤ zenithW G e u r:=by unfold zenithW courseWind vealS; positivity

variable [NormedAddCommGroup V][NormedSpace ℝ V]
structure Gale (o:Cover)(η:ℝ)(u:ℕ)(P:Ten V (YForest G) (r+1))(A:ℝ): Prop where
   nn:0≤ A
   windS i: rance o η u (fun x=>windsL x i P) A
lemma north_rance (a:G.Color){P:Gen V (YForest G)} (p:Fruit o η u (P (r-k+1)) A)(h:0≤η)(hq:η≤1): rance o η u (fun x=> northL k x a P r) (courseWind a k u r*A):=by
   unfold northL courseWind; simp_rw [Finset.sum_apply,Finset.sum_mul, Pi.add_apply]; refine rance.sum (P:=fun (i:Axis) (x:Cover)=>∑ j:G.ColorIndex,(wickLamp a 0 (x,i) j k P r + wickLamp 0 a (x-step i,i) j k P r)) ?_ h; intro i _
   apply rance.sum (P:=fun j x=>_) _ h; intro j _; rw [add_mul,mul_assoc]; exact (wick_rance a 0 i j p h).plus ((wick_rance 0 a i j p h).token i h hq) h
omit [NormedSpace ℝ V] in lemma Gale.step {P:Ten V (YForest G) (r+1)}(p:Gale o η u P A)(q:A≤B): Gale o η u P B:= ⟨p.nn.trans q,fun i=> (p.windS i).epochT q⟩
omit [NormedSpace ℝ V] in lemma Gale.shave {P: Ten V (YForest G) (r+1)}(p:Gale o η u P A)(he:0≤ σ)(hv:σ≤η): Gale o σ u P A:= ⟨p.nn,fun i=> Award.less (p.windS i) (fun _=>autumn_shrink he hv ..) (fun _=>zero_le_one.trans (autumn_pos he ..))⟩
lemma Gale.summer {P:Pal V (YForest G)}(p:vertical P)(q:∀ i,Pure (P i))(w:∀ i<e,∀ j≤ r+1,Fruit o η u (P i j) A)(h:0≤η)(hv:η≤1)(ha:0≤A) : Gale o η u (P e (r+1)) (zenithW G e u r*A):=by
    set S:= (Finset.antidiagonal e).erase (0,e); let b (i:G.ColorIndex) := coatC G (Pi.single i 1); let M (i:G.ColorIndex):= ∑ j∈ S,courseWind (b i) j.1 u r
    have ht : 0<((r+1:ℕ):ℝ):=by positivity
    let L:= ((r+1:ℕ):ℝ)⁻¹; refine ⟨mul_nonneg (costW_nn ..) ha,?_⟩; intro i
    set T:= P e (r+1); set a:= b i
    have hb : rance o η u (fun x=>(∑ j∈S,northL j.1 x a (P j.2)) r) (M i*A):=by
        unfold M; simp_rw [Finset.sum_apply,Finset.sum_mul]; refine rance.sum (S:=S) (M:=fun j=>courseWind (b i) j.1 u r*A) (P:=fun (k:ℕ×ℕ) (x:Cover)=>northL k.1 x a (P k.2) r) ?_ h; intro j hj; obtain ⟨hu,hv'⟩:= Finset.mem_erase.mp hj; have ht:= Finset.mem_antidiagonal.mp hv'
        have hq : j.1≠0:= fun h=> hu (Prod.ext h (show j.2=e from by omega))
        exact north_rance a (w _ (by omega) _ (by omega)) h hv
    have H x : windsL x i T = -L • (∑ j∈ S,northL j.1 x a (P j.2)) r:= by
        have he:= essence p q x i e r; rw [← Nat.cast_smul_eq_nsmul (R:=ℝ)] at he
        rw [neg_smul, ← smul_neg, ←he, smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
    have hp:= hb.scaled (-L); rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr ht.le)] at hp; simp_rw [H]; apply rance.epochT hp
    rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ ha; exact Finset.single_le_sum (f:=fun i=>L*M i) (fun i _=>by unfold L M courseWind vealS; positivity) (Finset.mem_univ i)

omit [NormedSpace ℝ V] in lemma beam_r (P:Ten V (YForest G) (r+1))(p:Gale o η u P A)(i:Fin (r+1))(h:0≤η): Fruit o η u (ledger P i) (Fintype.card (G.ColorIndex×Axis)* A):=by
    let W:=G.ColorIndex × Axis
    let Q:=visitJ (YForest G) i
    let J:=(((Equiv.prodAssoc W Cover (dock Cover (Hooks G) r)).symm.trans (Equiv.prodCongr (booths G) (Equiv.refl _))).trans (Equiv.prodComm ..)).trans Q
    let f x:= hedge o η u x* ‖ledger P i x‖
    have hp (m:W) : SumBudget (fun x=> f (J (m,x))) A := by
        obtain ⟨m,l⟩:=m; apply budget_minor (p.windS m) (fun x=>mul_nonneg (hedge_nn h _) (norm_nonneg _)); intro x; unfold ledger
        split; swap; · rw [norm_zero,mul_zero]; exact (p.windS m).1 x
        let y:=x.2; let v:= waive x.1 l m
        rw [show J _ = enlist i v y from rfl,outside,enlist_it]
        have hh:= stance_eq o v y; unfold enlist hedge; rw [tread_perm,hh]; exact le_rfl
    rw [←nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]; exact cap_walk f _ J (fun _=>rfl) (finance_terms hp)

-- for smooth see filter cut. Doesn't require exponential standby, lines just bounded.
variable [CompleteSpace V]
lemma switch_costR (i:Fin (r+1)){w:Site L}{K: Fin (r+1)→ ropes Cover (Co L (Hooks G)) (Hooks G)}{W: ropes Cover (Co L (Hooks G)) (Hooks G)}{P: Ten V (YForest G) (r+1)}(k:Fruit (L.val • o+lift w) (η/L.val) u P A)(p:∀ j,dragCup Bank.terrain s B (K j))(q:dragCup Bank.terrain s B W)(e:Smooth P){Z:ReaderT L G}(g: verdant (K i) W Z)(h:Gale (L.val • o+lift w) (η/L.val) u P C)(hz:dragCup Bank.terrain s B Z)(hs:0<s)(he:0≤η)(hu:η≤1): let R j:= owns L (K j) j; Fruit o η u (pump P (Function.update R i (owns L W i))-pump P R) ((B*tender (Hooks G) s u)^(r+1)*(9^u*(Fintype.card (G.ColorIndex × Axis) * C))):=by
    intro R; let T:= Function.update K i (assumeU Z); let F:= ledger P i; let V':=owns L W i-R i; let Y:= Function.update R i V'
    let E:= Function.update K i W; have hh : (fun i=> owns L (E i) i)=Function.update R i (owns L W i):=by
       funext j; unfold E; by_cases h:i=j; · subst j; rw [Function.update_self,Function.update_self]
       rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h)]
    have hE j:dragCup Bank.terrain s B (E j):= by
       unfold E; by_cases h:j=i; · subst j; rw [Function.update_self]; exact q
       rw [Function.update_of_ne h]; exact p _
    have hv j:dragCup Bank.terrain s B (T j):= by
       unfold T; by_cases h:j=i; · subst j; rw [Function.update_self]; exact ⟨hz.1,fun _ _=> hz.2 ..⟩
       rw [Function.update_of_ne h]; exact p _
    let S:=fun j=> owns L (T j) j
    have hT : S=Function.update R i (apex i (fun _ x j=>spring L Z (well x j))):=by
       unfold S; funext j; unfold T; by_cases h:j=i; · rw [h,Function.update_self,Function.update_self,flagL]
       rw [Function.update_of_ne h, Function.update_of_ne h]
    have hf:= beam_r P h i (show 0≤η/L.val by positivity)
    have hS:= roses _ hs _ hv hf he hu; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hS
    have ha x: spinJob P Y x= spinJob P (fun j=> owns L (E j) j) x-spinJob P R x:=by
       rw [hh]; funext y; rw [spin_replace,Pi.sub_apply,spin_replace]; unfold spinJob; rw [update_prod _ i]; unfold V'; rw [Pi.sub_apply,Pi.sub_apply,sub_mul,sub_smul]
    have hb x : Summable (spinJob P (fun i=> owns L (E i) i) x):=(pump_fin _ hs hE k he hu x).of_norm
    have hc x : Summable (spinJob P R x):=(pump_fin K hs p k he hu x).of_norm
    rw [show pump P (Function.update R i _) -_= pump P Y from ?_]
    · rw [show pump P Y= -(pump F S) from ?_]; exact Award.minus hS
      ext1 x; unfold Bank.pump; apply eyeY i
      · rw [ha]; exact (hb x).sub (hc x)
      · exact (pump_fin T hs hv hf he hu x).of_norm
      intro t; cases isEmpty_or_nonempty (YForest G); · simp
      next h0=>
       let k':= Classical.arbitrary (YForest G); set A':= ∏ j∈Finset.univ.erase i, R j (enlist i k' t) (x j)
       let J:=visitJ (YForest G) i
       have hu' (z:YForest G): ∏ j∈Finset.univ.erase i,R j (enlist i z t) (x j)=A':=by
          apply Finset.prod_congr rfl; intro j hj; unfold R owns; rw [remote (Finset.mem_erase.mp hj).1 t z k']
       let c y j:= A' * spring L Z (well y j) (x i)
       have H (F:Ten V (YForest G) (r+1)) (z:YForest G): spinJob F S x (enlist i z t)= c z.1 z.2.2 • F (enlist i z t):=by
          rw [hT,spin_replace,hu']; unfold c apex; rw [outside,enlist_it,mul_comm]
       have hX : Summable (spinJob P Y x):=by rw [ha]; exact (hb x).sub (hc x)
       apply tally2 i e c t _ _ ((J.summable_iff.mpr hX).prod_factor t) ((J.summable_iff.mpr (pump_fin T hs hv hf he hu x).of_norm).prod_factor t) _ (H F) (((J.summable_iff.mpr (pump_fin T hs hv k he hu x).of_norm).prod_factor t).congr (H P))
       intro y j d; change spinJob P (Function.update R i V') x (enlist i (waive y d j) t)=_; rw [spin_replace,hu']; unfold c V' R; rw [Pi.sub_apply,Pi.sub_apply, owns,owns,enlist_it,g,mul_comm,mul_sub]
    rw [←hh]; ext1 x; rw [Pi.sub_apply,Bank.pump,Bank.pump,Bank.pump,ha]; exact ((hb x).tsum_sub (hc x)).symm
end YM.WilsonCoeffUV.Shard
