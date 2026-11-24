import YM.OPE.Loom.Prices
/-!
# Read at fixed exterior hall and supply canonical physical reports
Non-finite and arbitrary exterior depth statements use a different path. Here
only fixed clearances, and for that any probes (must fit). -/
set_option autoImplicit false
noncomputable section
open Filter Function Set MeasureTheory
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid ManyCopies Next.Rank Next.UVStress PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker Cells Extraction
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{T:Table C.book}{F:Spec.Final C f T}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "δ" => renal C.path.levels
set_option quotPrecheck false
variable {𝓛:Filter (ℕ×ℕ)} {B:Frame.Scheme F} (L:Origins B 𝓛)
variable {I J: Type} [Fintype I][Fintype J] {v ε a b : ℝ} {f' k j m d : ℕ}
variable (s:I→ T.Tag) (u:I→ C.book.Token) {x:I→ Cover} {p:T.Field d}
structure Pack (F:Spec.Final C f T) (a:ℝ)(D:J→T.Tag) (m:ℕ) (c:ℝ) : Prop where
    options : ∃ v l b n :ℕ, Cards.Hall C.S v l m b n 1 (Fintype.card J) ∧ 2*C.S.a v < a ∧
       ∃ g:J→ℝ, OPE.Prepared (C:=C) (Frame.deploy ∘ D) f n g ∧ (∏ j,g j) ≤ c
structure Meets (F:Spec.Final C f T)(s:I→ T.Tag) (x:I→ E4) (p:T.Field d) (a b:ℝ)(m:ℕ) : Prop where
    all (J:Type)[Fintype J] (r:J→ T.Tag)(c:ℝ) (hc:Pack F a r m c) (y:J→E4)(w:Viewers F)(hp:Apart a y)(ht:ApartFrom a (sole (0:E4)) y) (hz: Injective (beside x y)) :
       ‖Frame.sense (spectator F w) (beside x y) (beside s r)-Frame.sense (spectator F w) (beside (sole (0:E4)) y) (beside (sole ⟨d,p⟩) r)‖ ≤ b*c
include L
lemma proposes (H:Org.Grill C f) (he:T.classTokens ∘ u=s) (p':C.label d) (P:ReadLabel C u)(hp:∀ i,Tendsto (P i) 𝓛 (𝓝 (u i).2))(h: Screen (C.S.gridPoint j ∘ x)) (hz:m≤j)(hM:MatchesHere u 𝓛 k j d m P x p' ε b): Meets F s (C.S.gridPoint j ∘ x) (T.project d p') a b m:=by
   constructor; intro J hi r g hg y w hs hx hY
   obtain ⟨v,l,t,n,hv,hB,G,hG,hd⟩:= hg.options
   have hv':v ≤ l:= hv.first.trans hv.second; have ha':2*C.S.a l ≤ a:= (mul_le_mul_of_nonneg_left ((S).strictAnti.antitone hv') zero_le_two).trans hB.le
   have hw':0 ≤ v:= Nat.zero_le _
   obtain ⟨π,z,hπ,hP,hz',ht⟩:= hM.buys
   let U:= spectator F w
   have he₀ : ∀ i, T.classTokens (Frame.deploy (r i))=r i:= fun i=>Frame.classify (r i)
   let p₀:C.book.Token:=⟨d,p'⟩; let y₀ := sole (0:E4)
   have hZ:Injective (beside y₀ y):= hx.together (show 0 ≤ a from (mul_pos zero_lt_two (C.S.a_pos v)).le.trans hB.le) (injective_of_subsingleton _) (hs.coin ((mul_pos zero_lt_two (C.S.a_pos v)).le.trans hB.le))
   rw [show beside s r = T.classTokens ∘ (beside u (Frame.deploy ∘ r)) from (by rw [beside_commutes,he,show T.classTokens ∘ Frame.deploy ∘ r=r from funext he₀]), show beside (_:Unit→ T.Tag) r =T.classTokens ∘ beside (sole p₀) (Frame.deploy ∘ r) from (by rw [beside_commutes,show T.classTokens ∘ Frame.deploy ∘ r=r from funext he₀]; rfl),Frame.as_token _ (spectate F _).laws.toSymmetric (spectate_respects F _) hY,Frame.as_token _ (spectate F _).laws.toSymmetric (spectate_respects F _) hZ]
   rw [← glance_sees F w _ _ hY,← glance_sees F w _ _ hZ, ← map_sub]
   apply le_trans (glance_bound ..); refine (current_space F H P ((hv.first.trans hv.third).trans hz) h (fun i j he=> lt_of_le_of_lt ha' (hs i j he)) (fun i j=>hB.trans (hx i j)) hY hv (hP.trans L.extraction) hz' (fun i=>(hp i).mono_left hP) (ht.mono fun _ h=>h.2) hG).trans (mul_le_mul_of_nonneg_left hd ht.exists.choose_spec.2.cost)

omit L
-- packed arbitrary fixed exterior (hall clearance a), all large enough m permit, uniformly in exterior names (pay card etc in n,c choice). also use `offset` facts for projections detector costs.
include F
lemma halls (ha:0<a) : ∀ᶠ m:ℕ in atTop, ∀ (J:Type)[Fintype J](D:J→T.Tag),∃ c:ℝ,Pack F a D m c := by
   let S':= C.S; obtain ⟨v,hv⟩:= (S'.shrinks.eventually (gt_mem_nhds (show 0 < a/2 by linarith))).exists
   have he : 2*C.S.a v < a:= by change C.S.a v < a/2 at hv; linarith
   obtain ⟨l,hl,hP⟩:= ((eventually_ge_atTop v).and (S'.shrinks.eventually (gt_mem_nhds (show 0 < S'.a v/11 by have := S'.a_pos v; positivity)))).exists
   filter_upwards [eventually_ge_atTop l] with m hm J hi D; let A:= Frame.deploy ∘ D
   obtain ⟨B,b,hB⟩:= admitted (T:=C.S.scale) F A S'.divergent first_price (by norm_num : (0:ℝ) < 1); have hp:S'.a l>0:=S'.a_pos _; let U (k):=(Fintype.card J:ℝ)*(2*(3*(S').a k))
   have hU:Tendsto U atTop (𝓝 0):= by convert! tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_const_nhds.mul C.S.shrinks)) using 1; simp -- rephrase
   obtain ⟨n,hQ,hN,hB'⟩:= ((hU.eventually (gt_mem_nhds hp)).and ((eventually_ge_atTop l).and hB)).exists; refine ⟨_,v,l,l,n,⟨hl,le_rfl,hm,hN,?_,hQ⟩,he,B n,hB',le_rfl⟩; change S'.a l<S'.a v/11 at hP; norm_num; linarith only [hP,hp]
end YM.OPE.Loom
