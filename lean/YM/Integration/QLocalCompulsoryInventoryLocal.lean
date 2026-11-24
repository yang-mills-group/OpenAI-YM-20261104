import YM.Integration.QLocalCompulsoryInventoryBank
import YM.Comparison.Density.Markers.Bounds

/-! A signed flag insertion supported at its physical owner produces a legal
native marked band on the original forced addresses at all fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalCompulsoryInventoryLocal
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open Comparison.Density.Markers QLocalCompulsoryInventoryProduct QLocalCompulsoryInventoryBank
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {P:Rep G n}

structure Captured (a:Bands Γ P) (h:Site n→ Config G n→Poly Γ) : Prop where
  roots i ξ : ξ∈(P.activities.forced i).inventory → ∀ U,
    Carries (fun v=>{a.origins v}) (P.activities.forced i).support (h ξ U)
  reads i ξ : ξ∈(P.activities.forced i).inventory →
    UsesFinal P.p.threshold (P.activities.forced i).support (h ξ)
  measurable ξ : Measurable (h ξ)
  invariant ξ : GaugeInvariant (h ξ)

private theorem old_roots {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {P:Rep G n} (a:Bands Γ P) (A:a.Active) (i:ℕ) (U:Config G n)
    (sum:Summable (fun j=>a.tagged i j U)) :
    Carries (fun v=>{a.origins v}) (P.activities.forced i).support (a.each i U) := by
  intro s v hv out
  have hn:s≠Γ.quiet:=fun hs=>by simp [hs,Census.quiet] at hv
  have row (j:ℕ):(a.tagged i j U).part s=0:=by
    rw [Bands.tagged,Poly.part_send]
    split
    next eq=>
      by_contra nz
      have live:a.entries i j≠0:=fun he=>nz (by rw [he];rfl)
      exact out (Finset.singleton_subset_iff.mpr (A.retained i j live v (eq ▸ hv)))
    rfl
  rw [Bands.each,Poly.part_plus,Poly.share sum,Poly.part_send,if_neg hn]
  simp only [row,tsum_zero,zero_add]

private theorem old_reads {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {P:Rep G n} (a:Bands Γ P) (A:a.Active) (K:P.activities.ForcedFamily P.p) (i:ℕ) :
    UsesFinal P.p.threshold (P.activities.forced i).support (a.each i) := by
  intro U W agree flags
  unfold Bands.each
  rw [K.reads i U W agree flags]
  congr 1
  exact tsum_congr fun j=>congrArg (Poly.send (a.marks i j)) (A.inspects i j U W agree flags)

private theorem old_invariant {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {P:Rep G n} (a:Bands Γ P) (A:a.Active) (K:P.activities.ForcedFamily P.p) (i:ℕ) :
    GaugeInvariant (a.each i) := by
  intro g U
  unfold Bands.each
  rw [K.sym i g U]
  congr 1
  exact tsum_congr fun j=>congrArg (Poly.send (a.marks i j)) (A.invi i j g U)

private theorem old_measurable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {P:Rep G n} (a:Bands Γ P) (A:a.Active) (K:P.activities.ForcedFamily P.p) (i:ℕ) :
    Measurable (a.each i) :=
  ((Bands.sends Γ.quiet).measurable.comp (Complex.continuous_ofReal.measurable.comp (K.meas i))).add
    (Measurable.tsum (fun j=>(Bands.sends (a.marks i j)).measurable.comp (A.meas i j)))

private theorem barred {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {P:Rep G n} (a:Bands Γ P) (A:a.Active) (K:P.activities.ForcedFamily P.p) (i:ℕ)
    (U:Config G n) (bar:¬(P.activities.forced i).eligible P.p.threshold U) : a.each i U=0 := by
  have hK:P.activities.K i U=0:=by_contra fun h=>bar (K.permit i U h)
  have hj (j:ℕ):a.entries i j U=0:=by_contra fun h=>bar (A.keeps i j U h)
  simp [Bands.each,Bands.tagged,hK,hj]

theorem original (a:Bands Γ P) (A:a.Active) (K:P.activities.ForcedFamily P.p)
    (sum:∀i U,Summable (fun j=>a.tagged i j U)) (i:ℕ) :
    (∀U,Carries (fun v=>{a.origins v}) (P.activities.forced i).support (a.each i U)) ∧
    UsesFinal P.p.threshold (P.activities.forced i).support (a.each i) ∧
    GaugeInvariant (a.each i) ∧ Measurable (a.each i) :=
  ⟨fun U=>old_roots a A i U (sum i U),old_reads a A K i,old_invariant a A K i,old_measurable a A K i⟩

theorem extra_roots (a:Bands Γ P) (A:a.Active) (h:Site n→ Config G n→Poly Γ) (S:Captured a h)
    (i:ℕ) (U:Config G n) (sum:Summable (fun j=>a.tagged i j U)) :
    Carries (fun v=>{a.origins v}) (P.activities.forced i).support (extra a h i U) := by
  have H:Carries (fun v=>{a.origins v}) (P.activities.forced i).support (localCharge P h i U):=
    Carries.sum _ (fun ξ hx=>S.roots i ξ hx U)
  exact ((Carries.pass _ _ _ H).sub carry_unit).mul (old_roots a A i U sum)

theorem active (a:Bands Γ P) (A:a.Active) (K:P.activities.ForcedFamily P.p)
    (h:Site n→ Config G n→Poly Γ) (S:Captured a h)
    (summable:∀i U,Summable (fun j=>a.tagged i j U)) : (bands a h).Active := by
  have loc (i:ℕ):UsesFinal P.p.threshold (P.activities.forced i).support (extra a h i):=by
    intro U W same flags
    have he:localCharge P h i U=localCharge P h i W:=
      Finset.sum_congr rfl (fun ξ hi=>S.reads i ξ hi U W same flags)
    rw [extra,extra,he,old_reads a A K i U W same flags]
  have gau (i:ℕ):GaugeInvariant (extra a h i):=by
    intro g U
    have he:localCharge P h i (gauge g U)=localCharge P h i U:=
      Finset.sum_congr rfl (fun ξ _=>S.invariant ξ g U)
    rw [extra,extra,he,old_invariant a A K i g U]
  have meas (i:ℕ):Measurable (extra a h i):=by
    have ml:Measurable (localCharge P h i):=Finset.measurable_fun_sum _ (fun ξ _=>S.measurable ξ)
    exact ((Poly.pass_cont.measurable.comp ml).sub measurable_const).mul (old_measurable a A K i)
  have original_entry (i l : ℕ) : (bands a h).entries i (roster Γ (.inl l))=a.entries i l := by
    funext U
    simp [bands,entry]
  have quiet_entry (i : ℕ) : (bands a h).entries i (roster Γ (.inr Γ.quiet))=fun _=>0 := by
    funext U
    simp [bands,entry]
  have joined_entry (i : ℕ) (s : Γ.Mode) (hs : s≠Γ.quiet) :
      (bands a h).entries i (roster Γ (.inr s))=fun U=>(extra a h i U).part s := by
    funext U
    simp [bands,entry,hs]
  refine ⟨A.proper,A.pins,A.regular,?_,?_,?_,?_,?_,?_⟩
  · intro i j
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>simpa [bands,mode] using A.occurs i l
    | inr s=>
      by_cases hs:s=Γ.quiet
      · simpa [bands,mode,hs] using A.occurs i 0
      · simpa [bands,mode,hs] using
          (Finset.nonempty_iff_ne_empty.mpr (fun e=>hs (Subtype.ext e)))
  · intro i j nz v hv
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>
      apply A.retained i l
      · rwa [original_entry] at nz
      · simpa [bands,mode] using hv
    | inr s=>
      by_contra no
      apply nz
      funext U
      by_cases hs:s=Γ.quiet
      · simp [bands,entry,hs]
      · have out:¬{a.origins v}⊆(P.activities.forced i).support:=fun ht=>no (Finset.singleton_subset_iff.mp ht)
        have used:v∈s.val:=by simpa [bands,mode,hs] using hv
        simp [bands,entry,hs,extra_roots a A h S i U (summable i U) s v used out]
  · intro i j U W same flags
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>simpa [bands,entry] using A.inspects i l U W same flags
    | inr s=>simp [bands,entry,loc i U W same flags]
  · intro i j U nz
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>exact A.keeps i l U (by simpa [bands,entry] using nz)
    | inr s=>
      by_contra bar
      exact nz (by simp [bands,entry,extra,barred a A K i U bar])
  · intro i j
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>rw [original_entry];exact A.meas i l
    | inr s=>
      by_cases hs:s=Γ.quiet
      · subst s;rw [quiet_entry];exact measurable_const
      · rw [joined_entry i s hs];exact (Poly.get s).continuous.measurable.comp (meas i)
  · intro i j g U
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>simpa [bands,entry] using A.invi i l g U
    | inr s=>simp [bands,entry,gau i g U]

end YM.Integration.QLocalCompulsoryInventoryLocal
