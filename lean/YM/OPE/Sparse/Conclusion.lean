import YM.OPE.Sparse.Evaluation
set_option quotPrecheck false

/-!
# Exact ratio prices along a designated physical ray

Use the same actual prescription on a general cluster tree when at most
one input is non-unit (e.g. unit dependencies may have positive uptake weights).
The exact unit cancellation is only used at admissible comparisons. Does
not handle genuintely multi-input singular price logging. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sparse
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Tracing Nesting.Motion
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
local notation "Q"=>U.sector.derivatives
namespace ExactPrice
open Circuit Evaluation
variable {n:ℕ}{f:Fin n→Nesting.Tree}(h:Services C F S)
local notation "nodes"=> Nesting.Tree.fork n f
variable (w:(Nesting.Tree.fork n f).Leaf→S.Tag) {m:ℕ} {D: (fork n f).Inner→ℕ}
variable (p:(fork n f).Leaf)(hw:Sparse w p)
local notation "trail"=> pathTree nodes p
local notation "turned" z => z ∘ layout nodes p
local notation "visit"=> (fun (_:(pathTree nodes p).Leaf)=>w p)
local notation "fj"=> fun (_:Fin 1)=>pathTree (f p.fst) p.snd
local notation "price"=> toll (wages w) (0:ℝ)
variable (i:R.channels m)(D){M η:ℝ}(hM:0≤M)(hη:0<η)
include h hM hη
private lemma fields_aux : ∃ c:ℝ,0<c ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,Accept x M η s z→ ‖Kernel.output U R (t:=trail) (turned z) visit i‖ ≤ c*price m s∧ ‖Kernel.output U R (t:=trail) (turned z) visit i-Kernel.chord U R (f:=fj) (turned z) visit i (D ∘ inlet nodes p)‖ ≤ c * bothToll (wages w) 0 m D s :=by
    let v: (pathTree nodes p).Leaf→ S.Tag:= fun _=>w p
    obtain ⟨c,hc,he⟩:=Measuring.scoop U R h |>.exact_path (f:=(fj)) (Tracing.narrow nodes p) hM hη v i (D ∘ inlet nodes p)
    refine ⟨c,hc,?_⟩
    filter_upwards [he,eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx h₀ s z hz
    have h:=hx (s ∘ inlet nodes p) (turned z) (fits nodes p hz)
    have h':=(Tracing.Price.allows p s (hz.levels.mono le_rfl h₀) (wages w) (fun i=>Nat.cast_nonneg _) (wages w p) le_rfl m)
    have hf: bothToll (wages v) 0 (m:ℝ) (D ∘ inlet nodes p) (s ∘ inlet nodes p) ≤ bothToll (wages w) 0 (m:ℝ) D s :=by
       let D':=D ∘ inlet nodes p; let u:=s ∘ inlet nodes p
       unfold bothToll
       have hu:0≤ nestPrice u D':=by
          apply Finset.sum_nonneg; intro p hp
          exact pow_nonneg (Measuring.Tree.tempered (tapered _ _ (hz.levels.mono le_rfl h₀)) one_pos (.inr p)).1.le _ -- named arg
       exact mul_le_mul h' (Tracing.Price.saving p _ (hz.levels.mono le_rfl h₀) D) hu (nonneg _ (hz.levels.mono le_rfl h₀))
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_left h' hc.le),h.2.trans (mul_le_mul_of_nonneg_left hf hc.le)⟩
where nonneg {n':ℕ}{f:Fin n'→Tree} (w) {s} {ε m:ℝ} (h:Tapered (fork n' f) 1 1 s) : 0≤ toll (f:=f) w ε m s:=by unfold toll; have he:=Measuring.Tree.tempered h one_pos; exact mul_nonneg (Real.rpow_nonneg (h.positive (.inl ()) |>.le) _) (Finset.prod_nonneg fun i _=>Real.rpow_nonneg (he (.inr i)).1.le _)

private lemma residual_aux {J:Type}[Fintype J](d:J→S.Tag){δ:ℝ}(hc:0<δ):∃ c:ℝ,0<c ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s: (fork n f).Inner→ℝ,∀ z:(fork n f).Plot,∀ y:J→E4,Accept x M η s z → Buffer z y δ → ∀ q:Viewers U, ‖Kernel.pipe U R (t:=trail) (turned z) visit q m y d‖ ≤ c*price (m+1:ℕ) s:=by
    obtain ⟨c,hc',hg⟩:=Measuring.scoop U R h |>.exact_tested (f:=fj) (Tracing.narrow nodes p) hM hη visit d hc m; refine ⟨c,hc',?_⟩
    filter_upwards [hg, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx hP s z y hz hy q
    have hu:=((hx (s ∘ inlet nodes p) (turned z) y) (fits nodes p hz) ⟨fun i j=>hy.1 _ _,hy.2⟩).2.2.2 q
    have hh:= mul_le_mul_of_nonneg_left (Tracing.Price.allows p s (hz.levels.mono le_rfl hP) (wages w) (fun i=>Nat.cast_nonneg _) (wages w p) le_rfl (m+1:ℕ)) hc'.le
    exact hu.trans hh

section Nonempty
include hw
lemma fields : ∃ K:ℝ,0<K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,Accept x M η s z →‖Kernel.output U R z w i‖ ≤ K*price m s ∧ ‖Kernel.output U R z w i - Kernel.chord U R z w i D‖ ≤ K* bothToll (wages w) 0 m D s:=by
     obtain ⟨K,hK,hg⟩:=fields_aux U R h (w:=w) (D:=D) (p:=p) (i:=i) hM hη; refine ⟨K,hK,?_⟩
     filter_upwards [hg, (uniform U R h).direct n f w m i D M η 1 hM hη one_pos] with x hx hm s z hz
     rw [leading U R (m:=m) w _ hw (hm s z hz).1, stacking U R w (hm s z hz).2.1 _ hw]; exact hx _ _ hz

lemma match'(m:ℕ) {J:Type}[Fintype J](d:J→S.Tag){δ:ℝ}(hc:0<δ):∃ K:ℝ,0<K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s: (fork n f).Inner→ℝ,∀ z:(fork n f).Plot,∀ y:J→E4, Accept x M η s z → Buffer z y δ → let k:=K*price (m+1:ℕ) s; ‖Kernel.normData U R z w m y d‖ ≤ k ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z w q m y d‖ ≤ k:=by
     obtain ⟨K,hK,hg⟩:=residual_aux U R h w p hM hη (m:=m) d hc; refine ⟨K,hK,?_⟩
     filter_upwards [hg, (uniform U R h).tested n f J w d m M η 1 δ hM hη one_pos hc, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx hm hP s z y hz hy; let k:=K*price (m+1:ℕ) s
     have ht:= (hm _ _ y hz hy).1; have hq q := stream U R w (z:=z) p hw d q (D':=m) ht.2.1 ht.1 |>.symm ▸ hx _ _ y hz hy q
     have hnonnegative:0≤ k:=mul_nonneg hK.le (fields_aux.nonneg (wages w) (Tapered.mono hz.levels le_rfl hP))
     refine ⟨(glance_contract U hnonnegative).mpr (fun q=>?_ ),hq⟩
     unfold Kernel.normData; erw [(formula_seen U R (y:=y) _ _ _ _ m _ ht.2.1 ht.2.2)]; exact hq q
end Nonempty

structure Voids:Prop where
    empty':IsEmpty (Nesting.Tree.Leaf (Nesting.Tree.fork n f))
variable (h':Voids (n:=n) (f:=f))
section
include h'
private lemma without(z:(fork n f).Leaf):False:= h'.empty'.false z
end
omit h hM hη in
private lemma safe {x:ℝ}{s: (fork n f).Inner→ℝ}{z: (fork n f).Plot}(hx:Accept (t:=nodes) x M η s z)(he:x≤1)(A:ℝ): x^(A-weight (degrees w)) ≤ price A s:=by
    have hp:s (Sum.inl ())=x:=hx.scale
    unfold toll; rw [sub_zero,show ∑ p, (wages w p:ℝ)=weight (degrees w) from rfl,hp]
    apply le_mul_of_one_le_right (Real.rpow_nonneg ((hx.levels.positive (.inl ()) |>.trans_eq hp).le) _) (Finset.one_le_prod (fun i hi=> ?_))
    have ht:=Measuring.Tree.tempered (hx.levels.mono le_rfl he) one_pos
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (ht _).1 (ht _).2
    rw [sub_zero]; have he:= Measuring.Tree.head_cast (fork n f) (degrees w) (.inr i)
    exact neg_nonpos.mpr ((Nat.cast_nonneg _).trans_eq he)

omit hw in
lemma empty_fields_aux (h'is:∀p:(fork n f).Leaf,literal (w p)) : ∃ K:ℝ,0<K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,Accept x M η s z →‖Kernel.output U R z w i‖ ≤ K*price m s ∧ ‖Kernel.output U R z w i - Kernel.chord U R z w i D‖ ≤ K* bothToll (wages w) 0 m D s:=by
      let K:ℝ:= max ‖R.coef m i (sole 0) (sole (S.unit 0):Labels S fun _:Unit=>0) 0‖ 1; have hK:=show 0<K from zero_lt_one.trans_le (le_max_right ..)
      refine ⟨K,hK,?_⟩
      filter_upwards [(uniform U R h).direct n f w m i D M η 1 hM hη one_pos, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx h₀ s z hz
      specialize hx s z hz
      have ht:=Measuring.Tree.tempered (hz.levels.mono le_rfl h₀) one_pos
      have hp:0≤ bothToll (wages w) 0 m D s:=mul_nonneg (fields_aux.nonneg (wages w) (ε:=0) (m:=m) (hz.levels.mono le_rfl h₀)) (Finset.sum_nonneg (fun l _=>by change 0 ≤ ((_root_.YM.OPE.Nesting.Tree.ratios nodes 1 s (Sum.inr l))^_); apply pow_nonneg ((ht (Sum.inr l)).1.le)))
      rw [full_unit U R w hx.2.1 h'is hx.1, sub_self,norm_zero, and_iff_left (mul_nonneg hK.le hp)]
      cases m with
      | zero=>rw [constant_unit U R w h'is hx.1]; apply (le_max_left ..).trans (le_mul_of_one_le_right hK.le (?_)); exact (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hz.levels.positive (.inl ()) |>.trans_eq hz.scale) h₀ (show (0:ℝ)-weight (degrees w) ≤ 0 from sub_nonpos.mpr (Finset.sum_nonneg (s:=Finset.univ) fun i hi=>Nat.cast_nonneg _))).trans (by simpa only [Nat.cast_zero] using (safe w hz h₀ 0))
      | succ m=>rw [killed U R w h'is hx.1 (Nat.zero_lt_succ _) i, norm_zero]; exact mul_nonneg hK.le (fields_aux.nonneg (wages w) (hz.levels.mono le_rfl h₀))

-- remove arbitrary losses on the complete error if there are *no* leaves;
-- single estimate through m+1 suffices before the remaining (only ratio) factors
include h' in
lemma no_test (m:ℕ) {J:Type}[Fintype J](v:J→S.Tag){δ:ℝ}(hc:0<δ):∀ᶠ x:ℝ in 𝓝[>]0,∀ s: (fork n f).Inner→ℝ,∀ z:(fork n f).Plot,∀ y:J→E4,Accept x M η s z → Buffer z y δ → let k:=1*price (m+1:ℕ) s; ‖Kernel.normData U R z w m y v‖ ≤ k ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z w q m y v‖ ≤ k:=by
      filter_upwards [(uniform U R h).tested n f J w v (m+1) M η 1 δ hM hη one_pos hc, quantitative_separated U R h (voices w) (voices v) (ε:=1) hM hη one_pos (m+1) hc,eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with x hx h₀ h₁ s z y hz hy
      let k:=1*price (m+1:ℕ) s
      let hi(p:(fork n f).Leaf):False:=h'.empty'.false p
      have he(i): Kernel.output U R z w i=0:=killed U R (m:=m+1) w (fun p=>(hi p).elim) ((hx s z y hz hy).1.1 _ le_rfl) (Nat.zero_lt_succ m) i
      have he' q:Kernel.pipe U R z w q m y v=formula U R (Tree.profile z) (anchor z) (voices w) y (voices v) (m+1) q:=by
          unfold Kernel.pipe formula Orbits.trunc; conv_rhs => rw [Fin.sum_univ_castSucc]; simp [show ∀ c:R.channels (m+1), R.coef (m+1) c (Tree.profile z) (voices w) (anchor z)=0 from he]
          rfl
      obtain ⟨hxy,hzy,-,hs⟩:= h₀ (Tree.profile z) (anchor z) y ⟨fun p=>(hi p).elim,fun i=>(hi i).elim⟩ ⟨fun j=>hy.1 _ j,hy.2⟩
      have h':(↑(m+1:ℕ):ℝ)+1-weight (degrees w)-1 = ↑(m+1:ℕ)-weight (degrees w):=by ring
      have H(q):= (hs q).trans (h'.symm ▸ ((safe w hz h₁ (m+1:ℕ)).trans_eq (one_mul _).symm))
      refine ⟨?_,fun q=>(he' q).symm ▸ H q⟩
      have hn:0 ≤ k:= (norm_nonneg _).trans (H none)
      apply (glance_contract U (c:=k) hn).mpr fun q=>(congr_arg norm (formula_seen U R _ _ _ y _ m _ hxy hzy)).trans_le <| ((congr_arg norm (he' q)).trans_le (H q))
end ExactPrice
end YM.OPE.Sparse
