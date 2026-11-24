import YM.Frontier6.Pair.Contexts
import YM.MergeProof.West.Puppy

/-!
# Fixed-cap phase readings and rough caps in actual engineering weights

All cost exponents may depend on a finite family, independent of phase.
The cost form with `Note.pitch` is intentionally for arbitrary horizon and
real x, not point estimates bounded only case-by-case.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Set Function Filter MeasureTheory Analysis Table Ward Climb Cells Next.UVStress Wilson Lattice Extraction.Around MergeProof MergeProof.Accent MergeProof.Ribbons OS Platform Spec
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G} {S:Table C.book} {F:Extraction.Order}
variable (K:Final C F S) (s:StateIndex K)
variable {n m :ℕ}

-- Geometry in the actual L² norm
def minGap (a:ℝ) (x:Points n):Prop:=∀ i j,i ≠ j → a < ‖x j-x i‖
def clearC (a:ℝ) (x:Points n):Prop:=minGap a (Points.cons 0 x)
theorem gap_conf {a:ℝ} (ha:0 ≤ a) {x:Points n} (hx:minGap a x) : x∈conf n:= fun i j he=> by_contra fun h=> (lt_of_le_of_lt ha (hx i j h)) |>.ne' (by rw [← he];simp)
theorem gap_down {a b:ℝ}{x:Points n}(h:minGap a x)(he:b≤a): minGap b x:= fun i j hi=>lt_of_le_of_lt he (h i j hi)
theorem gap_absent (a:ℝ)(n:ℕ) : IsOpen {x:Points n | minGap a x}:= by
    rw [show {x:Points n|_}= ⋂ (i:Fin n)(j:Fin n)(_ : i ≠ j), {x:Points n| a < ‖x j-x i‖} by ext; simp [minGap]]
    exact isOpen_iInter_of_finite fun i=> isOpen_iInter_of_finite fun j=> isOpen_iInter_of_finite fun h=> isOpen_lt continuous_const (by fun_prop)
theorem gap_append {a:ℝ}{x:Points n}(h:minGap a x)(y:E4)(he:∀ i:Fin n, a < ‖x i-y‖) : minGap a (Points.cons y x):= by
    intro i j; refine Fin.cases (motive:=fun i=> i≠j→ a < ‖Points.cons y x j-Points.cons y x i‖) (?_) (fun k=> ?_) i
    · refine Fin.cases ?_ (fun j=> ?_) j; simp; intro _; simpa [Points.cons] using he j
    refine Fin.cases ?_ (fun j=> ?_) j;swap
    · intro h';exact h k j (fun H=> h' (congr_arg _ H))
    simp [Points.cons,norm_sub_rev y,he]
theorem gap_compact {L : Set (Points n)}(h:IsCompact L)(hp:L ⊆ conf n): ∃ c:ℝ,0 < c∧ ∀ x∈L,minGap c x := by
    rcases L.eq_empty_or_nonempty with r|r; · exact ⟨1,one_pos,fun x hx=> (r ▸ hx : x∈(∅: Set _)).elim⟩
    have ht (i j:Fin n)(hi:i ≠ j) : ∀ᶠ a in 𝓝[>] (0:ℝ),∀ x∈L,a< ‖x i-x j‖ := by
       obtain ⟨x,hx,he⟩:= h.exists_isMinOn r (show Continuous (fun x:Points n=> ‖x i-x j‖) by fun_prop).continuousOn
       filter_upwards [show ∀ᶠ t:ℝ in 𝓝[>] 0, t < ‖x i-x j‖ from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr ((show Injective _ from hp hx).ne hi))))] with t ht y hy using ht.trans_le (he hy)
    obtain ⟨a,ha,hp⟩:= ((show ∀ᶠ t:ℝ in 𝓝[>] 0, 0<t from self_mem_nhdsWithin).and (eventually_all.mpr fun i=> eventually_all.mpr fun j=>eventually_all.mpr (ht i j))).exists
    exact ⟨a,ha,fun x hx i j h=> hp j i h.symm x hx⟩

noncomputable def reading (x:E4) (y:Points n) (v:Fin n→ S.Tag) (d:ℕ): S.Field d →L[ℂ] ℂ:=
    LinearMap.toContinuousLinearMap (((state K s).injectFront (expose ∘ v) (Points.cons x y) d) ∘ₗ (S.representative d))
lemma reads_at (x:E4)(y:Points n)(v:Fin n→ S.Tag) (d:ℕ)(B:S.Field d):
    reading K s x y v d B=S.useAt (state K s) (Points.cons x y) (Fin.cons ⟨d,B⟩ v):=by
     -- use injectFront
     change (state K s).read _ (Fin.cons ⟨d,S.representative d B⟩ _) = (state K s).read _ (expose ∘ Fin.cons (α:=fun _:Fin (n+1)=> S.Tag) ⟨d,B⟩ v)
     congr 1; ext1 i; refine Fin.cases ?_ (fun j=> ?_) i <;> rfl

def pairRead {d t:ℕ} (B:S.Field d)(U:S.Field t)(v:Fin n→ S.Tag)(x c:E4)(y:Points n):= reading K s x (Points.cons c y) (Fin.cons ⟨d,B⟩ v) t U
lemma cost_unit (x:E4)(y:Points n)(v:Fin n→ S.Tag) (d:ℕ)(B:C.label d) (hp:Points.cons x y ∈ conf (n+1)):
    reading K s x y v d (S.project d B)=(state K s).read (Points.cons x y) (Fin.cons ⟨d,B⟩ (expose∘v)):=by
    let P:S.Tag:= ⟨d,S.project _ B⟩
    have hq: Fin.cons P v=S.classTokens ∘ (Fin.cons (α:=fun _:Fin (n+1)=> C.book.Token) ⟨d,B⟩ (expose ∘ v)):= by
       ext1 i; refine Fin.cases ?_ (fun j=>?_) i
       · rfl
       simp only [Function.comp_apply, Fin.cons_succ]; change v j=⟨(v j).1,S.project _ (S.representative _ _)⟩; rw [S.rep]
    rw [reads_at, show Fin.cons (α:=fun _=>S.Tag) ⟨d,_⟩ v=Fin.cons P v from rfl,hq]; exact S.at_project _ (hierarchy K s).laws.toSymmetric (respects K s) hp _
lemma pair_reads {d t:ℕ} (B:S.Field d)(U:S.Field t)(v:Fin n→ S.Tag)(x c:E4)(y:Points n): pairRead K s B U v x c y=S.useAt (state K s) (Points.cons x (Points.cons c y)) (Fin.cons ⟨t,U⟩ (Fin.cons ⟨d,B⟩ v)):= reads_at ..
lemma pair_actual {d t:ℕ} (B:S.Field d)(U:S.Field t)(v:Fin n→ S.Tag)(x c:E4)(y:Points n): pairRead K s B U v x c y=(state K s).read (Points.cons x (Points.cons c y)) (seatsPair (C:=C) (seatsPair (expose ∘ v) ⟨d,S.representative _ B⟩) ⟨t,S.representative _ U⟩):=by
   change (state K s).read _ (Fin.cons ⟨t,_⟩ (expose ∘ Fin.cons (α:=fun _ :Fin (n+1) => S.Tag) ⟨d,B⟩ v))=_
   congr 1; ext1 i; refine Fin.cases ?_ (fun j=>?_) i; · rfl
   refine Fin.cases ?_ (fun k=>?_) j <;> rfl

variable (v:Fin n→ S.Tag)
noncomputable def totalGrade : ℕ:= MergeProof.Ribbons.Clouds (C:=C) (Ward.expose ∘ v)

open Org in
lemma tower_rough (hg:Grill C F) : ∃ a: ℕ→ℝ, Note C.S a (totalGrade v)∧ ∀ᶠ m:ℕ in atTop, ∀ s:StateIndex K,∀ x:Points n,slide C.S m x→ ‖S.useAt (state K s) x v‖ ≤ a m :=by
    obtain ⟨d,hd⟩:= Platform.fit_chart C.S n
    exact ⟨fun m=> honor C.S (expose∘v) (m+d),Note.longer (C:=C) (Note.glory v) d,state_budget (C:=C) (K:=K) hg (expose ∘ v) _ hd⟩

open Org in
lemma fields_rough (hg:Grill C F) (a:Fin n→S.Tag) (c:ℝ) (hc:0 < c) : ∃ B:ℝ, 0 ≤ B∧ ∀ s:StateIndex K, ∀ x:Points n,minGap c x→ ‖S.useAt (state K s) x a‖ ≤ B:=by
    obtain ⟨v,hv,H⟩:=tower_rough K a hg
    have hp:∀ᶠ m in atTop,4*C.S.a m ≤ c:= (C.S.shrinks.const_mul (4:ℝ)).eventually (ge_mem_nhds (by rw [mul_zero]; exact hc))
    obtain ⟨k,hk,h⟩:= (H.and hp).exists
    exact ⟨_,(hv.pos k).le,fun s x hx => hk s x (gap_down hx h)⟩

open Org in
lemma reading_bounded (hg:Grill C F) (v:Fin n→ S.Tag) (c:ℝ)(hc:0 < c)(d:ℕ) : ∃ B:ℝ, 0 ≤ B ∧ ∀ s:StateIndex K, ∀ (x:E4)(y:Points n),minGap c (Points.cons x y) → ‖reading K s x y v d‖ ≤ B:=by
    let L:=S.Field d; let Y:= Module.finBasis ℂ (S.Field d); let ι:=Fin (Module.finrank ℂ (S.Field d))
    choose B hB hp using fun (i:ι)=> fields_rough K hg (Fin.cons (α:=fun _=>S.Tag) ⟨d,Y i⟩ v) c hc
    let C i:= LinearMap.toContinuousLinearMap (Y.coord i)
    refine ⟨∑ i:ι, ‖C i‖*B i,Finset.sum_nonneg (fun i _=> mul_nonneg (norm_nonneg (C i)) (hB i)),fun s x y hx=>ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg (C i)) (hB i)) (fun p=>?_)⟩
    let R:= reading K s x y v d
    have hp'(i:ι):‖R (Y i)‖ ≤ B i:=by rw [show R _= _ from reads_at ..]; exact hp i _ _ hx
    have hu:R p=∑ i:ι,C i p • R (Y i):=by
       conv_lhs => arg 2; rw [← Y.sum_repr p]
       simp only [map_sum,map_smul]; rfl
    change ‖R _‖ ≤ _; rw [hu,Finset.sum_mul]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; rw [norm_smul]; exact (mul_le_mul ((C i).le_opNorm p) (hp' i) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
end YM.Frontier6
