import YM.SchemeConversionRG11.FirstW.Trice.Emboss
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {W:Wash}{R:ℝ}{n:Side}
lemma tick_any {P:Fin 3}(h:P≠0) : P=1∨P=2:= (full_order 0 P).resolve_left h
lemma atrium (hp:p∈conf 3)(a:At G 3 6)(he:a∈apart G 6 0)(k j:Who G 6) : amount p (dict a (dict (0,k) (dict (0,j) (SlateZ G))))=0:=by
 obtain ⟨i,a⟩:=a; rcases tick_any (show i≠0 from (Finset.mem_filter.mp he).2) with rfl|rfl
 all_goals rw [at0 (SlateZ G),at0]
 · rw [at1]; exact (erased_1 p hp a k j).1
 rw [at2]; exact (erased_1 p hp a k j).2
lemma near_stamp (i:P)(x:Full.Grid n 3)(he:i≠0)(F:Labels.Frames G)(hg:G.Simple)(q:ℝ)(U:Sky G (Per n))(h:∀ u: G.El,∀ a b c,U (putting u a) (putting u b) (putting u c)=U a b c) : group2 (SlateZ G) x q i U=0:=by
 rw [net_print (k:=basic F i)]; rotate_left; · exact (congrFun (basic_eq F).symm i)
 · exact hg
 · exact h
 unfold trestle; have hz(a b c :Who G 6):= tangI F a b c (basic F i) 4 (by decide) (Triangle.lower_basic _ _ he)
 simp [glist,hz]
lemma nil_morn (W:Wash) (F:Labels.Frames G) (i:P)(h:i≠0)(g:G.Simple)(k:ℕ)(T:Itinerary)(u:∀ i,Full.Grid (T.period i) 3): morn (SlateZ G) (u k) (T.gap k) i (currents W T u i k)=0:= by
 let A:=lapSky G (T.period k); let B:=currents (G:=G) W T u i k
 have hv(u:G.El)(X Y Z:FullT G (T.period k)): A (putting u X) (putting u Y) (putting u Z)= A X Y Z:= by unfold A lapSky; simp only [LinearMap.sum_apply,tower_key]
 have he(c:G.El)(X Y Z:FullT G (T.period k)): B (putting c X) (putting c Y) (putting c Z)= B X Y Z:= by
    unfold B currents deckP; simp only [LinearMap.coe_mk,AddHom.coe_mk, LinearMap.comp_apply, LinearMap.compl₂_apply]; simp only [wash_eq, show ∀ A:FullT G (T.period k),terms (u k i) (putting c A)=putting c (terms (u k i) A) from fun _=>rfl,tower_key]
 let P:=SlateZ G
 rw [show morn _ _ _ _ _=group2 P (u k) (T.gap k) i A-group2 P (u k) (T.gap k) i B from ?_]; simp only [P, near_stamp i _ h F g _ _ hv,near_stamp i _ h F g _ _ he,sub_zero]
 unfold morn group2; simp_rw [←Finset.sum_sub_distrib,add_sub_add_right_eq_sub]; simp only [verbD,stagedV,A,P,B,mul_sub]
lemma blip_morning (h:G.Simple)(F:Labels.Frames G)(d:Diorama T u p)(v:P)(he:W.rOut<R)(ht:∀ i j:P,i≠ j → 8*R<‖p i-p j‖)(hc:MarkGrid T c) : Tendsto (fun i=>morn (SlateZ G) (u i) (T.gap i) v (currents W T u v i)) atTop (𝓝 0):= by
 by_cases hv:v=0; swap; · simp_rw [nil_morn _ F _ hv h]; exact tendsto_const_nhds
 subst v; unfold morn; apply tend_t; intro a _; apply tend_t; intro b _; apply tend_t; intro s hs
 let X:=SlateZ G; let P:=dict s (dict (0,b) (dict (0,a) X))
 have H:= ht 0 s.1 (Ne.symm (Finset.mem_filter.mp hs).2)
 obtain ⟨z,hz⟩:= upkeep W d 0 a b (e:=s) (lt_trans (show R<8*R by linarith [W.rOut_pos]) H) he hc
 let Z:= fun i=> crossQ T (forth T u (0,a)) (forth T u (0,b)) (forth T u s) W (fun i=>u i 0) i
 have ht:= fortune d P; rw [show amount p P=0 from atrium d.ht s hs b a] at ht
 have hZ:= ((continuous_ofReal.continuousAt.tendsto.comp hz).mul ht).const_mul (3:ℂ); rw [mul_zero,mul_zero] at hZ
 simp_rw [verbD,stagedV, ←sub_mul, ← ofReal_sub];exact hZ
lemma closed_fee (F:Labels.Frames G)(h:G.Simple)(d:Diorama T u p)(W:Wash)(he:W.rOut<R)(ht:∀ i j:P,i≠j→8*R<‖p i-p j‖)(hc:MarkGrid T c)(Z:ℕ→Pack F)(hz:stampB F Z T W):
 Tendsto (fun i=> showP T F u (basic F) Z i-(flowV (SlateZ G) (u i) (T.gap i)+flowC (SlateZ G) (u i) (T.gap i))) atTop (𝓝 0):= by
 let X:= SlateZ G
 let U(j:Fin 3)(s:ℕ):=costCT F W T j u Z (basic F j) X s
 let V(j:Fin 3)(s:ℕ):=morn X (u s) (T.gap s) j (currents W T u j s)
 have H:= stock_puck F (basic F) d W Z h; dsimp only at H; rw [basic_eq] at H
 have he(j:Fin 3): Tendsto (fun s=> U j s+ V j s) atTop (𝓝 0):=by
    let p':=billedC F W T u Z (basic F j) X j; have hv:= (remains d X j (basic F j) (congrFun (basic_eq F).symm j) W he (fun i hi=>ht i j hi) Z hz h hc).cheap; have hp := burn_tax p d j he ht hc Z hz; have hs:= (hv.add hp).add (blip_morning (W:=W) h F d j he ht hc); rw [add_zero,add_zero] at hs; apply hs.congr; intro s; change U j s - p' s + billedC F W T u Z (basic F j) (SlateZ G) j s + V j s= _; unfold p' X; rw [sub_add_cancel]
 have hx:= H.cheap.add (tend_t Finset.univ (fun j s=> U j s+ V j s) (fun j _=>he j)) -- needs fun j _
 rw [zero_add] at hx; apply hx.congr; intro i; unfold showP U V X; abel
end YM.RG11.FirstW.Branch
