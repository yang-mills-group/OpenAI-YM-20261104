import YM.Comparison.RG02.Valence.Level
import YM.Comparison.RG02.Cumulants.Wick
/-! Charge internal legs in *connected log* computation. Wick mean reads still committed on a single
    joint prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick
open YM.Extra.Trajectories (connected connected_quiet)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff

variable {V I J : Type} [DecidableEq V] [DecidableEq I] {R : Census V}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (loc : I→V) (idx : I→ J) (Q : Normal.Symmetric J) (μ : E→J→ℂ) (hμ : ∀ j, Level 1 (fun x=> μ x j))
include hμ
private lemma cardinal (s : R.Mode) (A : Finset V) (p : Finset I) (r : ℕ) : Level (((p.card:ℕ):ℤ)+ 2*A.card-2*s.val.card) (fun x : E => trees loc idx Q (μ x) s A p r) := by
   induction r generalizing A p with
   | zero=>
     by_cases hp:(legs loc p A).Nonempty
     · simp_rw [trees,dif_pos hp]; exact Level.zero _
     simp_rw [trees,dif_neg hp]; split_ifs with he
     · subst A; exact (Level.constant 1).promote (by omega)
     exact Level.zero _
   | succ r ih=>
     by_cases hp:(legs loc p A).Nonempty
     · simp_rw [trees.eq_1 loc idx Q _ s A p (r+1),dif_pos hp]
       let i:= Classical.choose hp
       have hi:i∈p ∧ loc i∈A:= mem_filter.mp (Classical.choose_spec hp)
       have hk : (p.erase i).card=p.card-1:= card_erase_of_mem hi.1
       have hP:= card_pos.mpr (show p.Nonempty from ⟨i,hi.1⟩)
       apply Level.add
       · exact ((hμ (idx i)).mul (ih A (p.erase i))).promote (by omega)
       apply Level.total; intro j hj
       have hj':j∈p.erase i:= (mem_filter.mp hj).1
       have hl:= card_erase_of_mem hj'; have hh:= card_insert_le (loc j) A
       have hz:= card_pos.mpr (show (p.erase i).Nonempty from ⟨j,hj'⟩)
       exact ((ih (insert (loc j) A) ((p.erase i).erase j)).factor (Q.cov (idx i) (idx j))).promote (by omega)
     simp_rw [trees.eq_1 loc idx Q _ s A p (r+1),dif_neg hp]; split_ifs with he
     · subst A; exact (Level.constant 1).promote (by omega)
     exact Level.zero _

variable [Fintype V]
lemma vertex_count (s : R.Mode) (p : Finset I) : Level ((p.card:ℤ) + 2 - 2*s.val.card) (fun x=> (connected (moments R (Normal.blend Q (μ x)) (word loc idx p))).part s) := by
   by_cases h : s.val.Nonempty
   · obtain ⟨i,hi⟩:=h; simp_rw [connected_tree loc idx Q _ s i hi p p.card le_rfl]; simpa only [card_singleton,Nat.cast_one,mul_one] using cardinal loc idx Q μ hμ s {i} p p.card
   rw [of_not_not (mt (hot_iff_ne s).2 h)]
   have he(x:E): (moments R (Normal.blend Q (μ x)) (word loc idx p)).part R.quiet=1:=by rw [moments_quiet]; exact Normal.fresh ..
   simp_rw [connected_quiet (he _)]; exact Level.zero _

omit [DecidableEq I] in
lemma price_list (u : V→ℕ) (s : R.Mode) (Z : ∀ i, Fin (u i)→J) (v : ℤ)
    (hl : (∑ i∈s.val, (u i:ℤ)) + 2 - 2*s.val.card ≤ v) : Level v (fun x=> (connected (moments R (Normal.blend Q (μ x)) (fun i=> Normal.glyphs (Z i) univ))).part s) := by
  let p : Finset (Σ i:V,Fin (u i)) := s.val.sigma fun i=> univ
  let ψ: (Σ i:V,Fin (u i))→J:= fun i => Z i.1 i.2
  let L : (Σ i:V,Fin (u i))→V:= Sigma.fst
  have hg (i:V)(hi:i∈s.val): Normal.glyphs (Z i) univ=Wick.word L ψ p i:= by
     unfold word Normal.glyphs
     refine Finset.prod_bij (fun a _ => (⟨i,a⟩ : Σ i:V, Fin (u i))) (fun a _=> mem_filter.mpr ⟨mem_sigma.mpr ⟨hi,mem_univ _⟩,mem_singleton_self _⟩) (fun a _ b _ he=> Sigma.mk.inj_iff.mp he|>.2|>eq_of_heq) ?_ (fun _ _=>rfl)
     rintro ⟨k,b⟩ hb; have he:k=i:= mem_singleton.mp (mem_filter.mp hb).2; subst k; exact ⟨b,mem_univ _,rfl⟩
  have h(x:E): (connected (moments R (Normal.blend Q (μ x)) (fun i=>Normal.glyphs (Z i) univ))).part s = _ := equal_occurrences (Normal.blend Q (μ x)) _ _ s hg
  simp_rw [h]; apply (vertex_count L ψ Q μ hμ s p).promote
  simpa only [p,card_sigma,Finset.card_univ,Fintype.card_fin,Nat.cast_sum] using hl
end YM.Comparison.RG02.Valence
