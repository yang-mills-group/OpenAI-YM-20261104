import YM.SchemeConversionRG11.FirstW.Jade.Fog
import YM.SchemeConversionRG11.FirstW.Jade.Cost
import YM.SchemeConversionRG11.FirstW.Fade.Moons
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory Set Metric Lattice Pert Align Position Topology Maxwell MvPolynomial
open scoped BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side}{Q:Wash}{R:ℝ}{G:Gauge}{r:ℕ}{A B:Sight T G} {w:Points r}{u:∀ i,Full.Grid (T.period i) r}{F:Labels.Frames G}
lemma post_at (b c:At G r 6)(s:Fin r)(d:Diorama T u w)(hb:w b.1≠w s)(hc:w c.1≠w s)(a:Labels.Key G)(h:a.fst≤2) : Helen (fun i=> echoLeg (T.gap i) (u i s) a (arise (T.gap i) (u i) b) (arise (T.gap i) (u i) c)):= by
 let U(i:ℕ):= u i s; let x (a:At G r 6)(i:ℕ):= u i a.1; let A(a:At G r 6):= SeaA T a.2.val (x a-U)
 have he(a:At G r 6)(i:ℕ): nativeM T (A a) i=tracing (U i) (arise (T.gap i) (u i) a):= by
   change _ = passA T U (verdant T (x a) a.2.val) i; rw [move_ver]
   unfold nativeM A SeaA; rw [smul_inv_smul₀ (T.positive i).ne']; rfl
 let S:={y:E4| y≠ w b.1-w s} ∩ {y | y ≠ w c.1-w s}; have ht:0∈S:= ⟨(sub_ne_zero.mpr hb).symm,(sub_ne_zero.mpr hc).symm⟩
 obtain ⟨v,H⟩:= praises (A:=A b) (B:=A c) (riseP _ (looked d s b.1) _ inter_subset_left) (riseP _ (looked d s c.1) _ inter_subset_right) ht a h
 refine ⟨_,H.congr fun i=>?_⟩; simp only [he,echoLeg,LinearMap.smul_apply, echo_translate,zero_add,U]
lemma sparkle (d:Diorama T u w)(hg:G.Simple) (X:Fin r→E F 6): Helen (fun i=> flowC (cloak F ∘ X) (u i) (T.gap i)):= by
 let p:=cloak F ∘ X; change Helen (fun i=> flowC p _ _); unfold flowC; apply collectH; intro a _; apply collectH; intro b hb; apply collectH; intro c hc; let s:=a.1
 have hs: dict a p= update p s (D1 a.2 (p s)) := rfl
 by_cases e:a.2.val.1≤2
 · have h(i:At G r 6)(h:i∈Star3 a): w i.1 ≠ w s:=d.ht.ne (Finset.mem_filter.mp h).2 -- confirms
   obtain ⟨v,H⟩:= post_at b c s d (h b hb) (h c hc) a.2.val e; let q:=dict c (dict b (dict a p)); obtain ⟨z,hz⟩:= (show Helen (fun i=>ZeroR (u i) (T.gap i) q) from ⟨_, Warp.poly_limit 6 T _ _ d.ht d.hs d.hdiv (fun i=>uncap_height (q i))⟩); let F (i:ℕ):= echoLeg (T.gap i) (u i s) a.2.val (arise (T.gap i) (u i) b) (arise (T.gap i) (u i) c); have h : Tendsto (Complex.ofReal ∘ F) atTop (𝓝 (Complex.ofReal v)) := Complex.continuous_ofReal.continuousAt.tendsto.comp (show Tendsto F atTop _ from H)
   have hx(t:ℕ): changeD (u t) (T.gap t) p a b c = Complex.ofReal (F t)*ZeroR (u t) (T.gap t) q:=by unfold changeD; dsimp only [F,q,s]
   simp_rw [hx]; exact ⟨_,h.mul hz⟩
 have he (i:ℕ): changeD (u i) (T.gap i) p a b c=0:= by
   unfold changeD; rw [hs,dict_b p s b hb, dict_b _ s c hc, show D1 a.2 (p s)=0 from pder_end (X s) _ (Nat.lt_of_not_ge e) hg]; obtain ⟨L,hp⟩:= pays_slot (dict c (dict b p)) s (u i) (T.gap i); rw [← hp,map_zero,mul_zero]
 simp_rw [he]; exact ⟨_,tendsto_const_nhds⟩
lemma perk {f g:ℕ→ℂ}(h:Helen f)(hp:Helen g): Helen (fun i=> f i+g i):= by obtain ⟨x,X⟩:= h; obtain ⟨y,Y⟩:= hp; exact ⟨_,X.add Y⟩
lemma nipped {f g:ℕ→ℂ}(h:Helen g)(hp:Fleck T (fun i=>f i-g i)): Helen f:= by obtain ⟨x,X⟩:=h; have ht:= hp.cheap.add X; simpa only [sub_add_cancel] using! (show Helen _ from ⟨_,ht⟩)
def showP (T:Itinerary)(F:Labels.Frames G)(u:∀ i,Full.Grid (T.period i) r)(v:Fin r→E F 6)(z:ℕ→Pack F)(i:ℕ):= stock F _ (u i) (T.gap i) v (carryR (T.period i) (T.gap i) (z i))
lemma whole_at (d:Diorama T u w)(F:Labels.Frames G)(h:G.Simple)(v:Fin r→E F 6)(Q:Wash)(hq:Q.rOut<R)(hp:∀ i j:Fin r,i≠j → 8*R < ‖w i-w j‖)(hc:MarkGrid T c)(Z:ℕ→Pack F)(hz:stampB F Z T Q) : Helen (showP T F u v Z) := by
 let p:= cloak F ∘ v; have H:= stock_puck F v d Q Z h
 have he (i j: Fin r)(hh:i ≠ j): R< ‖w i-w j‖ := lt_trans (by linarith [Q.rOut_pos]) (hp i j hh)
 obtain ⟨X,Y⟩:=path_paid p d hq hc he
 apply nipped _ H; apply perk (perk X (sparkle d h v)); apply collectH; intro i _; exact perk (nipped (voltC d p i _ Q hq (fun j e=> hp j i e) Z hz hc) (remains d p i (v i) rfl Q hq (fun j e=> hp j i e) Z hz h hc)) (Y i)
end YM.RG11.FirstW.Deck
