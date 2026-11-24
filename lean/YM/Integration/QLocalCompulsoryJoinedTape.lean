import YM.Integration.QLocalMarkedJoinedSeries
import YM.Integration.QLocalCompulsoryInventoryLocal

/-! The original compulsory rows and their pre-existing marked entries
stay present while the coefficient of each new mode gets a distinct seat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalCompulsoryJoinedTape
open Function Finset Lattice RG Wilson Marker Overlay RG3.Script.Picnic
open LocalComparison Comparison.Density.Markers WilsonLimitConstruction.FundedMarkedFieldSplit
open QLocalCompulsoryInventoryBank (roster mode)
open scoped Classical BigOperators
variable {G:Gauge} {V X:Type} [DecidableEq V] [Fintype V] {Γ:Census V}
    {n:Side} {P:Rep G n} {o:V→Site n}

def entry (a:Bands Γ P) (d:ℕ→ Config G n→Poly Γ) (i j:ℕ) (U:Config G n) : ℂ :=
  Sum.elim (fun l=>a.entries i l U) (fun s=>if s=Γ.quiet then 0 else (d i U).part s)
    ((roster Γ).symm j)

def bands (a:Bands Γ P) (d:ℕ→ Config G n→Poly Γ) : Bands Γ P :=
  {a with marks:=mode a.marks,entries:=entry a d}

def tape (T:Taste X o P Γ) (d:X→ℕ→ Config G n→Poly Γ) : Compulsory X Γ G n :=
  ⟨mode T.menu.marks,fun x=>entry (T.menu.terms x) (d x)⟩

theorem terms {G:Gauge} {V X:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {n:Side} {P:Rep G n} {o:V→Site n} (T:Taste X o P Γ) (d:X→ℕ→ Config G n→Poly Γ) (x:X) :
    (replace T (tape T d)).menu.terms x=bands (T.menu.terms x) (d x) := rfl

theorem original {G:Gauge} {V X:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {n:Side} {P:Rep G n} {o:V→Site n} (T:Taste X o P Γ) (d:X→ℕ→ Config G n→Poly Γ) (x:X) (i j:ℕ) (U:Config G n) :
    (tape T d).mode i (roster Γ (.inl j))=T.menu.marks i j ∧
    (tape T d).value x i (roster Γ (.inl j)) U=T.menu.force x i j U  := by simp [tape,mode,entry];rfl

theorem tagged {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {n:Side} {P:Rep G n} (a:Bands Γ P) (d:ℕ→ Config G n→Poly Γ) (i:ℕ) (U:Config G n)
    (old:Summable (fun j=>a.tagged i j U)) : Summable (fun j=>(bands a d).tagged i j U) := by
  let g (v:ℕ⊕Γ.Mode):=(bands a d).tagged i (roster Γ v) U
  have main:Summable (fun l:ℕ=>g (.inl l)):=old.congr (fun l=>by simp [g,bands,mode,entry,Bands.tagged])
  have extra:Summable (fun s:Γ.Mode=>g (.inr s)):=(hasSum_fintype _).summable
  exact (roster Γ).summable_iff.mp (HasSum.sum (f:=g) main.hasSum extra.hasSum).summable

theorem each {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {n:Side} {P:Rep G n} (a:Bands Γ P) (d:ℕ→ Config G n→Poly Γ) (i:ℕ) (U:Config G n)
    (quiet:(d i U).part Γ.quiet=0) (old:Summable (fun j=>a.tagged i j U)) :
    (bands a d).each i U=a.each i U+d i U := by
  let f:ℕ⊕Γ.Mode→Poly Γ:=Sum.elim (fun j=>a.tagged i j U) (fun s=>Poly.send s ((d i U).part s))
  have seats (v:ℕ⊕Γ.Mode):(bands a d).tagged i (roster Γ v) U=f v:=by
    cases v with
    | inl j=>simp [bands,Bands.tagged,mode,entry,f]
    | inr s=>
      by_cases hs:s=Γ.quiet
      · subst s; simp [bands,Bands.tagged,mode,entry,f,quiet]
      · simp [bands,Bands.tagged,mode,entry,f,hs]
  have finite:HasSum (fun s=>Poly.send s ((d i U).part s)) (d i U):=by
    simpa only [Poly.studs] using hasSum_fintype (fun s=>Poly.send s ((d i U).part s))
  have both:HasSum f ((∑' j,a.tagged i j U)+d i U):=HasSum.sum (f:=f) old.hasSum finite
  have eq:(∑'j,(bands a d).tagged i j U)=(∑' j,a.tagged i j U)+d i U:=
    ((roster Γ).tsum_eq _).symm.trans ((tsum_congr seats).trans both.tsum_eq)
  exact congrArg (fun z=>Poly.send Γ.quiet (P.activities.K i U:ℂ)+z) eq |>.trans (add_assoc ..).symm

structure Eligible (a:Bands Γ P) (d:ℕ→ Config G n→Poly Γ) : Prop where
  roots i U : Carries (fun v=>{a.origins v}) (P.activities.forced i).support (d i U)
  reads i : UsesFinal P.p.threshold (P.activities.forced i).support (d i)
  permits i U : d i U≠0→(P.activities.forced i).eligible P.p.threshold U
  measurable i : Measurable (d i)
  invariant i : GaugeInvariant (d i)

theorem active {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {n:Side} {P:Rep G n} (a:Bands Γ P) (A:a.Active) (d:ℕ→ Config G n→Poly Γ) (E:Eligible a d) :
    (bands a d).Active := by
  have original_entry (i l : ℕ) : (bands a d).entries i (roster Γ (.inl l))=a.entries i l := by
    funext U
    simp [bands,entry]
  have quiet_entry (i : ℕ) : (bands a d).entries i (roster Γ (.inr Γ.quiet))=fun _=>0 := by
    funext U
    simp [bands,entry]
  have joined_entry (i : ℕ) (s : Γ.Mode) (hs : s≠Γ.quiet) :
      (bands a d).entries i (roster Γ (.inr s))=fun U=>(d i U).part s := by
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
      · simpa [bands,mode,hs] using (Finset.nonempty_iff_ne_empty.mpr (fun e=>hs (Subtype.ext e)))
  · intro i j nz v hv
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>exact A.retained i l (by rwa [original_entry] at nz) v (by simpa [bands,mode] using hv)
    | inr s=>
      by_contra no
      apply nz
      funext U
      by_cases hs:s=Γ.quiet
      · simp [bands,entry,hs]
      · have out:¬{a.origins v}⊆(P.activities.forced i).support:=fun ht=>no (Finset.singleton_subset_iff.mp ht)
        have use:v∈s.val:=by simpa [bands,mode,hs] using hv
        simp [bands,entry,hs,E.roots i U s v use out]
  · intro i j U W same flags
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>simpa [bands,entry] using A.inspects i l U W same flags
    | inr s=>simp [bands,entry,E.reads i U W same flags]
  · intro i j U nz
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>exact A.keeps i l U (by simpa [bands,entry] using nz)
    | inr s=>exact E.permits i U (fun zero=>nz (by simp [bands,entry,zero]))
  · intro i j
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>rw [original_entry];exact A.meas i l
    | inr s=>
      by_cases hs:s=Γ.quiet
      · subst s;rw [quiet_entry];exact measurable_const
      · rw [joined_entry i s hs];exact (Poly.get s).continuous.measurable.comp (E.measurable i)
  · intro i j g U
    obtain ⟨j,rfl⟩:=(roster Γ).surjective j
    cases j with
    | inl l=>simpa [bands,entry] using A.invi i l g U
    | inr s=>simp [bands,entry,E.invariant i g U]

end YM.Integration.QLocalCompulsoryJoinedTape
