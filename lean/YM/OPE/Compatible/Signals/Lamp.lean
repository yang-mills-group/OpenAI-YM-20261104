import YM.OPE.Compatible.Signals.Elite
/-!
# Simultaneous finite list of tests and quotient prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson Cells Extraction Word Spec OPE.Allot
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Final C F S)
variable (P: Prescription U.sector.derivatives)
-- simultaneous quote
local notation "L'"=> U.sector.derivatives
lemma tunes (d:ℕ)(h:Org.Grill C F) : ∀ᶠ k:ℕ in atTop, ∃ b A:ℝ, 0<b∧0≤A∧∀ {W:ℕ}, k ≤ W → ∀ {X:Type}[Fintype X][DecidableEq X]{x:X→ Cover}{n j:ℕ}{q:C.label j}{v p:X→ C.book.Token}{f g:ℝ}, (∀ i,S.classTokens (v i)=S.classTokens (p i)) → Survival (C:=C) F k n W f g v x j q → Screen (C.S.gridPoint W ∘ x) → (∀ i, ‖C.S.gridPoint W (x i)‖ < b) → ∀ a∈ bands L' d, ‖P.ope a (C.S.gridPoint W ∘ x) p 0-P.test a j (S.project j q)‖ ≤ f*A:=by
   let s:= bands L' d; filter_upwards [eventually_all.mpr (fun i:s=> tuning U P i.1 h)] with k hk
   choose b A hb hA hK using hk
   obtain ⟨t,ht,hq⟩:= ((show ∀ᶠ t:ℝ in 𝓝[>]0, 0<t from self_mem_nhdsWithin).and ((eventually_all.mpr fun i=> ge_mem_nhds (hb i)).filter_mono nhdsWithin_le_nhds)).exists
   refine ⟨t, ∑ i:s,A i,ht,Finset.sum_nonneg (fun _ _=>hA _),fun {W} hW X _ _ x n j q v p f g hh hp hx hr a ha=>?_⟩
   have hh0:0 ≤ f:=by obtain ⟨u,F,hf,_,_,hv,_⟩:=hp.wins; exact hv.receipt.exists.choose_spec.cost
   let i:s:= ⟨a,ha⟩; exact (hK i hW hh hp hx (fun j=> lt_of_lt_of_le (hr j) (hq i))).trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun q _=>hA q) (Finset.mem_univ _)) hh0)
namespace Arboreal
variable {V B J:Type}[PartialOrder V][OrderBot V][Fintype V]{ψ: Filter B}{T:B→ℝ}
variable [Fintype J]
variable (A:Allot C)(D:Origin V){Q:Finset V}(p:brim D Q → C.book.Token) (w:J→ C.book.Token)
variable {n d b:ℕ}{s:B→V→ℝ}{η M c:ℝ}
set_option quotPrecheck false
local notation "Ω"=> fun i=> volume D Q (fun a=> (p a).1) (s i)
local notation "R"=> fun i=> s i ⊥
lemma close_of_tend (hp : Crown Q) (h:Tendsto R ψ (𝓝[>] 0)) {b:ℝ}(he:0<b) : ∀ᶠ i in ψ,∀ x:V→E4, Ridge (s i) η M D Q x → ∀ j:brim D Q,‖x j‖< b:=by
    have hh : Tendsto (fun i=> M*R i) ψ (𝓝 0):=by simpa only [mul_zero] using ((h.mono_right nhdsWithin_le_nhds).const_mul M)
    filter_upwards [hh.eventually (gt_mem_nhds he)] with i hi x hx j; have he:= hx.near _ _ hp.base (Finset.mem_union_right _ j.2) bot_le; rw [hx.belly,zero_sub,norm_neg] at he; exact he.trans_lt hi
-- point handoff
variable (hΓ:Glowing D Q ψ T s η)(hI:Inward C F S)(hG:G.Simple)(h:Org.Grill C F)(hp:1 ≤ b)(hM:0 ≤ M)
include A hΓ hI hG hp hM h
local notation "j"=> fun i=> schedule C b η (s i) ⊥-1 -- harmless
lemma simultaneously (v d:ℕ)(hc:0<c) : ∃ B B' C₀: _→ℝ, Round ψ T (fun i=> B i*Ω i/R i^d)∧ Round ψ T (fun i=> B' i*Ω i/R i^d)∧ Round ψ T (fun i=> C₀ i*Ω i/R i^d)∧ ∃ k:ℕ,∀ᶠ i in ψ,∀ z: V → E4, Address C D Q v b (T i) (s i) η M z → ∃ W:ℕ, ∃ (x:brim D Q→ Cover)(p':brim D Q→ C.book.Token)(q:C.label d),
       Survival (C:=C) F k (j i) W (B' i) (C₀ i) p' x d q ∧ (∀ a ∈ bands L' d, ‖P.ope a (picked (brim D Q) z) p 0-P.test a d (S.project _ q)‖ ≤ B i)∧ ∀ y:J→ E4, ClearOf 0 y c → Injective (beside (picked (brim D Q) z) y)→ ∀ r:Viewers U, ‖observe (spectator U r) (beside (picked (brim D Q) z) y) (beside p w)-observe (spectator U r) (beside (sole (0:E4)) y) (beside (sole (⟨d,q⟩: C.book.Token)) w)‖≤B i := by
    obtain ⟨k,⟨t,M₀,ht,hM₀,hk⟩,M₁,hM₁,he⟩:= ((tunes U P d h).and (clear_of_res U w hc h)).exists
    obtain ⟨l,hl⟩:= A.buy.tabs.mayOpen C.path.levels 1 k
    obtain ⟨u,c',hu,hq,hG'⟩:= announce_here U A hG hI D p hΓ hM hp v (A.buy.tabs.open_later C.path.levels 1 hl (Nat.le_max_left l (C.ref d)) zero_le_one) (le_max_right ..)
    let B(i) := u i * (M₀+M₁+1); have hv0 : Round ψ T (fun i=> B i * Ω i / R i^d):=(hu.mul (Round.const (a:=M₀+M₁+1) (by positivity) hΓ.ray)).adjust (Eventually.of_forall fun i=> by unfold B; ring)
    refine ⟨B,u,c',hv0,hu,hq,k,?_⟩; filter_upwards [hG',close_of_tend D hΓ.crowned (η:=η) (M:=M) (hΓ.fade _ hΓ.crowned.base) ht] with i hi hh z hZ
    obtain ⟨W,x,p',q,hk',hg,hC,hS⟩:=hi z hZ
    let a := picked (brim D Q) z; have hY: Screen (C.S.gridPoint W ∘ x):= hg.symm ▸ hZ.screen
    have hf(a'): ‖C.S.gridPoint W (x a')‖ < t:=by change ‖(C.S.gridPoint W ∘ x) a'‖<_; rw [hg]; exact hh z hZ.ridge a'
    have h0:0 ≤ u i:=by obtain ⟨_,_,_,_,_,hz,_⟩:=hS.wins; exact hz.receipt.exists.choose_spec.cost
    refine ⟨W,x,p',q,hS, fun b hb=>?_,fun y hρ hv r=>?_⟩
    · rw [← hg]; exact (hk hk' hC hS hY hf b hb).trans (mul_le_mul_of_nonneg_left (by linarith : M₀≤M₀+M₁+1) h0)
    have hF:= he W hk' _ hS hY y hρ (hg.symm ▸ hv) r; rw [hg,sees_same (p:=beside p w) (v:=beside p' w) (spectate U r).laws.toSymmetric (spectate_respects U r) (fun i=>by cases i with
       | inl i=> exact hC i
       | inr => rfl) hv] at hF; exact hF.trans (mul_le_mul_of_nonneg_left (by linarith : M₁≤M₀+M₁+1) h0)
end Arboreal
end YM.OPE
