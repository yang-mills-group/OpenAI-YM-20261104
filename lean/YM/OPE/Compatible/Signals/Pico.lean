import YM.OPE.Compatible.Signals.Lamp
/-! Uniform remainder with exactly one extra degree. Auxiliary spectra at maximal weight cost outward. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson Cells Extraction Word Spec OPE.Allot
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Final C F S)
variable (P: Prescription U.sector.derivatives)
local notation "L'"=> U.sector.derivatives
variable {J X:Type} [Fintype J] [Fintype X] [DecidableEq X]
variable {a:C.book.Token}(w:J→ C.book.Token) {x:X→E4}{y:J→ E4} {c:ℝ}
-- absolute independent ext
lemma page_fixed (v:C.book.Token)(h:Org.Grill C F)(hc:0<c): ∃ A:ℝ,0≤A ∧ ∀ y:J→E4, ClearOf (0:E4) y c → ∀ r:Viewers U, ‖observe (spectator U r) (beside (sole (0:E4)) y) (beside (sole v) w)‖ ≤ A:=by
    obtain ⟨b,hb⟩:= ((C.S.shrinks.const_mul 2).eventually (by rw [mul_zero]; exact gt_mem_nhds hc)).exists
    have hh:(Tendsto (fun i=> (↑(Fintype.card Unit):ℝ)*(2*(5*C.S.a i))) atTop (𝓝 0)):=by simpa only [mul_zero] using (((C.S.shrinks.const_mul 5).const_mul 2).const_mul (↑(Fintype.card Unit):ℝ))
    obtain ⟨i,he,hi,L,hL⟩:= ((hh.eventually (gt_mem_nhds (C.S.a_pos b))).and ((eventually_ge_atTop b).and (prepared_some U (sole v)))).exists; have hx:Tendsto (fun k=> (↑(Fintype.card J):ℝ)*(2*(3*C.S.a k))) atTop (𝓝 0):=by simpa only [mul_zero] using (((C.S.shrinks.const_mul 3).const_mul 2).const_mul (↑(Fintype.card J):ℝ))
    obtain ⟨j,hj,hn,Y,hY⟩:= ((hx.eventually (gt_mem_nhds (C.S.a_pos i))).and ((eventually_ge_atTop i).and (prepared_some U w))).exists; refine ⟨_,mul_nonneg hL.cost hY.cost,fun y hy r=>?_⟩
    have hd:Cards.Hall C.S b i i i j (Fintype.card Unit) (Fintype.card J):=⟨hi,le_rfl,le_rfl,hn,he,hj⟩; obtain ⟨hU,hT⟩:=hy.steered hb hi
    have hG:=civic U h (Apart.diagonal _ (sole (0:E4))) hU hT hd hL hY; have hz:= hT.together (mul_nonneg zero_le_two (C.S.a_pos _).le) (injective_of_subsingleton _) (hU.coin (mul_nonneg zero_le_two (C.S.a_pos _).le)); rw [← glance_sees U r _ _ hz]; exact (glance_bound ..).trans hG
lemma page_total (d:ℕ)(h:Org.Grill C F)(hc:0<c):∃ A:ℝ,0 ≤ A ∧ ∀ y:J→E4, ClearOf 0 y c → ∀ r:Viewers U, ∀ i∈ bands L' d, ‖observe (spectator U r) (beside (sole (0:E4)) y) (beside (sole (P.letter i)) w)‖ ≤ A:=by
   let s:=bands L' d; choose a ha hA using fun i:s=>page_fixed U w (P.letter i.val) h hc
   refine ⟨∑ i:s,a i, Finset.sum_nonneg (fun _ _=>ha _),fun y hv r i hi=>?_⟩; let x:s:=⟨i,hi⟩; exact (hA x y hv r).trans (Finset.single_le_sum (fun i _=>ha i) (Finset.mem_univ _))
-- cumulative grade
lemma mode_top (hO:Outward C F S L')(h:P.Coherent)(d:ℕ):∃ L:ℕ,∀ᶠ i:ℕ in atTop, ∀ a:Mode L', a.fst=d → ∀ {X: Type}[Fintype X][DecidableEq X]{x:X→ Cover} {k W:ℕ}{u p:ℝ}{z:X→ C.book.Token}{q:C.label d}, Survival (C:=C) F k i W u p z x d q → ‖P.test a d (S.project d q)‖ ≤ β C i^L*p:=by
   let s := bands L' d; choose L hL using fun i:s=>mode_paid U P h hO d i.val ((full_bands ..).1 i.2)
   refine ⟨Finset.univ.sup L,?_⟩; filter_upwards [eventually_all.mpr hL] with i hi a ha X _ _ x k W u p z q hs
   let j:s:=⟨a,(full_bands ..).mpr ha.le⟩; have he := hi j u p hs; have hh:j.val.fst=d:=ha; rw [hh,Nat.sub_self,pow_zero,mul_one] at he; refine he.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (β_one ..|>.le) (Finset.le_sup (Finset.mem_univ _))) ?_)
   -- use any present facet (in scope)
   exact nonneg_of_mul_nonneg_right ((norm_nonneg _).trans he) (pow_pos (β_pos ..) _)

lemma ClearOf.inject_both (h:ClearOf (0:E4) y c)(hc:0<c): Injective (beside (sole (0:E4)) y):=by
    have ht : Apart (0:ℝ) y:=fun _ _ hp=> hc.trans_le (h.spread _ _ hp); exact (show ApartFrom 0 (sole (0:E4)) y from fun _ j=> hc.trans_le (h.openSpace j)).together le_rfl (injective_of_subsingleton _) (ht.coin le_rfl)
-- small finite counting estimate
variable {d:ℕ}{B M u v:ℝ}
omit [DecidableEq X] in
lemma less_trunc (h:P.Coherent)(r:Viewers U) {p:X→ C.book.Token}(z:C.label (d+1)) (hy:Injective (beside (sole (0:E4)) y)) (ht:∀ i∈ bands L' d, ‖P.ope i x p 0 - P.test i _ (S.project _ z)‖ ≤ u) (hv:∀ i:Mode L', i.fst=d+1→ ‖P.test i _ (S.project _ z)‖ ≤ v) (hB:0≤B)(hb:∀ i∈ bands L' (d+1), ‖observe (spectator U r) (beside (sole (0:E4)) y) (beside (sole (P.letter i)) w)‖ ≤ B) :
    ‖observe (spectator U r) (beside (sole (0:E4)) y) (beside (sole (⟨d+1,z⟩: C.book.Token)) w) - P.truncated (spectator U r) d x p 0 y w‖ ≤ ↑((bands L' (d+1) \ bands L' d).card)*(v*B)+↑((bands L' d).card)*(u*B):=by
   have hs: bands L' d ⊆ bands L' (d+1):=fun i hi=> (full_bands ..).2 (((full_bands ..).1 hi).trans d.le_succ); let f i:=P.test i _ (S.project _ z); let g i:=P.ope i x p 0; let c i:=observe (spectator U r) (beside (sole (0:E4)) y) (beside (sole (P.letter i)) w)
   rw [← P.sumAll (spectator U r) w (spectate_ready U r) (spectate U r).laws.toSymmetric (spectate_respects U r) hy h z]; change ‖(∑ i∈ _,f i*c i)-(∑ i∈ _,g i*c i)‖ ≤ _
   rw [← Finset.sum_sdiff (f:=fun i=> f i*c i) hs,add_sub_assoc,← Finset.sum_sub_distrib]; apply (norm_add_le ..).trans; refine add_le_add ((norm_sum_le ..).trans ?_) ((norm_sum_le ..).trans ?_)
   · refine le_trans (b:=∑ i∈ (bands L' (d+1)\bands L' d), v*B) (Finset.sum_le_sum fun i hi=>?_) (by simp); obtain ⟨ha,hi⟩:= Finset.mem_sdiff.mp hi; have hp := ((full_bands ..).mp ha).antisymm (lt_of_not_ge (mt ((full_bands ..).2) hi)); rw [norm_mul]; exact ((mul_le_mul_of_nonneg_left (hb i ha) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (hv i hp) hB))
   refine le_trans (b:=∑ i∈ bands L' d, u*B) (Finset.sum_le_sum fun i hi=>?_) (by simp); rw [← sub_mul,norm_mul,norm_sub_rev]; exact ((mul_le_mul_of_nonneg_left (hb i (hs hi)) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (ht i hi) hB))
end YM.OPE
