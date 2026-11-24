import YM.OPE.Compatible.Signals.Clear
/-!
# Align complex readers on issued center, plan all tests first (finite lists at fixed clearance)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson Cells Extraction Word Spec
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {S : Table C.book}(U:Final C F S) {X J:Type} [Fintype X][Fintype J]
    (p: X→ C.book.Token) {x:X→ E4}
-- flexible projected slots
lemma sees_same {v:X→ C.book.Token} {A:Table C.book}(hs:A.Symmetric)(ha:A.respects S)(hv:∀ i,S.classTokens (v i)=S.classTokens (p i))(hx:Injective x) : observe A x v= observe A x p :=by
    rw [observe_exact A _ hs ha hx,observe_exact A _ hs ha hx]; exact congr_arg _ (funext fun i=>hv _)
-- clearance for fixed ext
lemma cleared (e:Exterior C.book): ∃ x:ℝ,0<x ∧ ClearOf (0:E4) (bearing e) x:=by
   obtain ⟨a,h,hc⟩:= Cov.RateLocations e (fun _:Unit=>1) (fun _: Unit=>(0:E4)) -- Ortho one
   refine ⟨a,h,?_⟩; specialize hc (); rwa [show (fun j=> _+ (0:E4)) = bearing e from funext fun i=> by simp [Cov.Survey.placements]] at hc
set_option quotPrecheck false
include U
lemma panel (e:Exterior C.book) (h:Org.Grill C F) : ∀ᶠ k:ℕ in atTop, ∃ b A:ℝ, 0<b∧0≤A∧∀ {W:ℕ}, k ≤ W → ∀ {X:Type}[Fintype X][DecidableEq X]{x:X→ Cover} {n d:ℕ}{q:C.label d}{p v:X→ C.book.Token} {f g:ℝ}, (∀ i,S.classTokens (p i)=S.classTokens (v i)) → Survival (C:=C) F k n W f g p x d q → Screen (C.S.gridPoint W ∘ x)→ (∀ i, ‖C.S.gridPoint W (x i)‖< b) → ‖Prescription.reading S (C.S.gridPoint W ∘ x) v 0 e - S.spectra d (S.project d q) e‖≤ f*A :=by
    obtain ⟨b,hb,hP⟩:= cleared e
    filter_upwards [clear_of_res U e.letter hb h] with k ⟨A,hA,hk⟩
    refine ⟨b,A,hb,hA,fun {W} hW X _ _ x n d q v p f g hh hs hx hr=>?_⟩
    have ht: Injective (beside (C.S.gridPoint W ∘ x) (bearing e)):= beside_distinct.mpr ⟨hx.coin,(beside_distinct.mp (bearing_clear e)).2.1,fun i j he=> by
       have hl:=hr i; change (C.S.gridPoint W) (x i)=_ at he; rw [he] at hl; have hz:=hP.openSpace j; rw [zero_sub,norm_neg] at hz; exact not_lt.mpr hz hl⟩
    have hy:= hk W hW v hs hx _ hP ht none -- likely v p swap: numbering
    rw [← Prescription.one_test d e q U.room.kernel]; unfold Prescription.reading; simp only [sub_zero,if_pos ht,if_pos (bearing_clear _),spectator, Option.elim_none] at *; rw [sees_same (v:=beside v e.letter) (p:=beside p e.letter) U.room.kernel.laws.toSymmetric (S:=S) (fun _=>le_rfl) (fun j=> by cases j with
       | inl j => exact hh j
       | inr=> rfl) ht] at hy; exact hy
-- aggregate current mode
lemma tuning (P:Prescription U.sector.derivatives)(a: Mode U.sector.derivatives)(h:Org.Grill C F) : ∀ᶠ k:ℕ in atTop, ∃ b A:ℝ, 0<b∧0≤A∧∀ {W:ℕ}, k ≤ W → ∀ {X:Type}[Fintype X][DecidableEq X]{x:X→ Cover}{n d:ℕ}{q:C.label d}{p v:X→ C.book.Token}{f g:ℝ},(∀ i,S.classTokens (p i)=S.classTokens (v i)) → Survival (C:=C) F k n W f g p x d q → Screen (C.S.gridPoint W ∘ x) → (∀ i,‖C.S.gridPoint W (x i)‖ < b) → ‖P.ope a (C.S.gridPoint W ∘ x) v 0 - P.test a d (S.project d q)‖ ≤ f*A := by
   let l := P.sheet a; let J : Type:= l.support
   filter_upwards [eventually_all.mpr fun j:l.support=>panel U j.val h] with k hk
   choose b A hb hA hV using hk
   have hs : ∀ᶠ t:ℝ in 𝓝[>] 0,0<t∧ ∀ j,b j ≥ t:= (show ∀ᶠ t:ℝ in 𝓝[>] 0,0<t from self_mem_nhdsWithin).and ((eventually_all.mpr fun j=> ge_mem_nhds (hb j)).filter_mono nhdsWithin_le_nhds)
   obtain ⟨b',hb',hj⟩:=hs.exists
   refine ⟨b',∑ i:l.support,‖l i‖*A i,hb',Finset.sum_nonneg (fun j _=> mul_nonneg (norm_nonneg _) (hA _)), fun {W} hW X _ _ x n d q p v f g hh hs hx hr=>?_⟩
   let t(j:Exterior C.book):ℝ:= if h:j∈l.support then f * A ⟨j,h⟩ else 0
   refine (near_shadow P v a (A':=S.project d q) (κ:=t) (fun i hi=>?_)).trans_eq ?_
   · unfold t; rw [dif_pos hi]; exact hV ⟨_,hi⟩ hW hh hs hx (fun i=> lt_of_lt_of_le (hr i) (hj _))
   rw [← Finset.sum_attach]; simp_rw [t]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [dif_pos i.2]; ring
end YM.OPE
