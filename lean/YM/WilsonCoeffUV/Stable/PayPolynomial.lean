import YM.WilsonCoeffUV.Stable.Wind
/-!
# Lower estimate at general Pal. Poly ℓ1 response constant at every change.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Wilson Tree Power PowerSeries Exterior Soil Precision Embroider Fountain Cosmos
open scoped Topology BigOperators
variable {L:Side}{U α V W ι : Type*}{i e k r u j l D:ℕ} {A B C s σ η δ : ℝ} {o:Cover}{G:Gauge}

def VectorWind [NormedAddCommGroup V](o:Cover)(η:ℝ)(u:ℕ)(A:ℝ): {r:ℕ}→ChamberTen G V r→Prop
   | 0,_=>0≤A
   | _+1,F=> Gale o η u F A
lemma VectorWind.pos [NormedAddCommGroup V]{P:ChamberTen G V r}(p:VectorWind o η u A P): 0≤A:=by cases r; exact p; exact Gale.nn p
lemma VectorWind.step [NormedAddCommGroup V]{P:ChamberTen G V r}(p:VectorWind o η u A P)(h:A≤B): VectorWind o η u B P:=by cases r; exact p.pos.trans h; exact Gale.step p h
lemma VectorWind.shave [NormedAddCommGroup V]{P:ChamberTen G V r}(p:VectorWind o η u A P)(h:0≤σ)(v:σ≤η):VectorWind o σ u A P:=by cases r; exact p; exact Gale.shave p h v
lemma VectorWind.summer [NormedAddCommGroup V][NormedSpace ℝ V]{P:Pal V (YForest G)} (p:vertical P)(q:∀ i,Pure (P i))(w:∀ i<e,∀ j≤r,Fruit o η u (P i j) A)(h:0≤η)(hv:η≤1)(ha:0≤ A): VectorWind o η u (zenithW G e u (r-1)*A) (P e r):=by cases r; exact mul_nonneg (costW_nn ..) ha; exact Gale.summer p q w h hv ha
-- arbitrary offset depth

def veilR (G:Gauge)(u:ℕ)(s B:ℝ)(r:ℕ):= (r:ℝ)*(B*tender (Hooks G) s u)^r*(9^u*Fintype.card (G.ColorIndex × Axis))
lemma veilR_nn (G:Gauge)(u:ℕ)(p:0<s)(h:0≤B)(r:ℕ): 0≤ veilR G u s B r:=by unfold veilR; have hv:=tender_nn p (Hooks G) u; positivity
lemma itR [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{w:Site L}{K W: ropes Cover (Co L (Hooks G)) (Hooks G)}{P: Ten V (YForest G) r}(k:Fruit (L.val • o+lift w) (η/L.val) u P A)(p:dragCup Bank.terrain s B K)(q:dragCup Bank.terrain s B W)(e:Smooth P){Z:ReaderT L G}(g: verdant K W Z)(h:VectorWind (L.val • o+lift w) (η/L.val) u C P)(hz:dragCup Bank.terrain s B Z)(hs:0<s)(he:0≤η)(hu:η≤1): Fruit o η u (pump P (owns L W)-pump P (owns L K)) (veilR G u s B r*C):=by
    cases r with
    | zero=> rw [show pump P (owns L W)= pump P (owns L K) from funext fun _=>by simp [pump,spinJob], sub_self, veilR,Nat.cast_zero,zero_mul,zero_mul,zero_mul]; exact Fruit.zero
    | succ r=>
      let M i (j:Fin (r+1)):= if j.val< i then W else K; let V i:= fun j=> owns L (M i j) j; let U:=(B*tender (Hooks G) s u)^(r+1)*(9^u*(Fintype.card (G.ColorIndex × Axis) * C))
      have hh:∀ i≤r+1,Fruit o η u (pump P (V i)-pump P (owns L K)) (i*U):=by
          intro i; induction i with
          | zero=> intro _; rw [show V 0= owns L K from funext fun i=>by simp only [V,M,Nat.not_lt_zero,↓reduceIte],sub_self,Nat.cast_zero,zero_mul]; exact Fruit.zero
          | succ i ih=>
            intro h'; let v: Fin (r+1):=⟨i,h'⟩
            have hM j: dragCup Bank.terrain s B (M i j):=by unfold M; split<;> assumption
            have hv: V (i+1)=Function.update (V i) v (owns L W v):=by
                funext j; by_cases h:j=v; · subst j; unfold V; rw [Function.update_self,show M (i+1) v=W from if_pos (Nat.lt_succ_self i)]
                rw [Function.update_of_ne h]; unfold V; congr 1; have ht:j.val≠i:= fun he=>h (Fin.ext he); simp only [M,show j.val< i+1↔ j.val< i from by omega]
            rw [Nat.cast_succ,add_mul,one_mul,add_comm _ U,show pump P _-_= pump P (V (i+1))-pump P (V i)+(pump P (V i)-pump P (owns L K)) from by abel, hv]; exact (switch_costR v k hM q e (by rw [show M i v=K from if_neg (lt_irrefl i)]; exact g) h hz hs he hu).plus (ih (by omega)) he
      specialize hh (r+1) le_rfl; rw [show V (r+1)= owns L W from funext fun i=>by unfold V; rw [show M (r+1) i=W from if_pos i.isLt]] at hh; unfold veilR; exact hh.more (le_of_eq (by unfold U; ring))

lemma feather_wet {Y:ChamberTen G (Vote D) r}(p:VectorWind 0 η u A Y)(h:0≤η)(P:Patch)(w:Site P.L):VectorWind (lift w) η u A (featherS P w Y):=by
   cases r with
   | zero=> exact p
   | succ r=>
     refine ⟨p.pos,fun i=>?_⟩
     let o:=lift w; let T:= soprano P w D; let F:=fun x k=> windsL x k Y
     have ht (y) (x) :windsL x i (featherS P w Y) y=T (F (-o+x) i (jog (-o) ∘ y)):=by
        let a:=-o+x; unfold F windsL T; simp only [Finset.sum_apply,map_sum,Pi.sub_apply, map_sub]; apply Finset.sum_congr rfl; intro b _
        unfold prune featherS revolve; rw [Function.comp_apply,Function.comp_apply]; congr 2
        · rw [← comps_head]; rfl
        rw [← comps_head]; congr 2; unfold jog stone; simp [o]; abel
     let Q : Equiv.Perm (Cover × dock Cover (Hooks G) r) := (Equiv.addLeft (-o)).prodCongr ((Equiv.refl _).arrowCongr (jog (-o)))
     let V (x:Cover × dock Cover (Hooks G) r):= F x.1 i x.2
     let v (x:Cover × dock Cover (Hooks G) r):= autumn η u (stance o x.1 x.2)
     have hv : Award (V ∘ Q) v A:= Award.pivot (s:=v) (Gale.windS p i) Q rfl (funext fun x=> congr_arg (autumn η u) (windy o x.1 x.2))
     unfold rance; simp_rw [ht]; exact Award.more (hv.touch T (fun _=>zero_le_one.trans (autumn_pos h ..))) (mul_le_of_le_one_left p.pos (budgetS ..))

lemma hall_turnR (P:Patch)(h:ℕ){Q K:Drip P G} {Y:ChamberTen G (Vote D) r}(p:0<s)(v:dragCup Bank.terrain s B Q)(u':dragCup Bank.terrain s B K)(z:ReaderT P.L G)(e:verdant Q K z)(hz:dragCup Bank.terrain s B z)(g:Smooth Y)(f: Fruit 0 (η/P.L.val) u Y A)(hg:VectorWind 0 (η/P.L.val) u C Y)(he:0≤η)(hu:η≤1): Fruit 0 η u (hall P h K Y-hall P h Q Y) ((P.L.val:ℝ)^h*(veilR G u s B r*C)):=by
   have hs:0≤η/P.L.val:=by positivity
   have hx (w:Site P.L): Fruit 0 η u (pulseS P w K Y-pulseS P w Q Y) (veilR G u s B r*C) := by
       let x:= lift w; have hp : Smooth (featherS P w Y):=fun σ a=>by unfold featherS revolve; rw [Function.comp_apply,Function.comp_apply,←Function.comp_assoc,g]
       exact itR (w:=w) (P:=featherS P w Y) (by rw [smul_zero,zero_add]; exact (Fruit.touch _ (by simpa only [add_zero] using f.turn x) hs)) v u' hp e (by rw [smul_zero,zero_add]; exact feather_wet hg hs P w) hz p he hu
   unfold hall; rw [←smul_sub (tiara P h) (_:ChamberTen G (Vote D) r),←Finset.sum_sub_distrib,←tier_cash]; exact (Fruit.sum (S:=Finset.univ) (fun w _=>hx w) he).μ _
end YM.WilsonCoeffUV.Shard
