import YM.OPE.Compatible.Maestro.Terminus
/-!
# Physical UV pricing inputs for logarithmic improvement

A priori a **conditional** strengthening route. Not used by
Spec.final, foundational compatible expansions, any rank/tables support,
sweeps, etc. Needed *quantitative matching* on the physical quotient; a
comparison only accurate to subpower with canonical fields at
individual UV heights may give no control of these directions.

Statements require actual trajectories. Representatives before taking
norms can vary with calls but projection after transport to selected
space is fixed. Mesh limits appear through the same Final schedule (not
its uniqueness). Spindle.paid includes the engineering currency, i.e.
a^-d above normalized quotient. Same purchase direction price feeds all
unions. Can formulate with any further sequence/subsequence providing
supports along the same Schwinger sheet.

The later estimates depend on these and we discharge
them in `Consumer.physical_estimates`. These are *not* asymptotic OPE
or factorization claims themselves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank.Spindle Next.UVStress
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot -- remove
variable {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
structure Inward (C:Family G)(F:Extraction.Order)(S:Table C.book) : Prop where
    allowed d (z:C.label d):∃ L:ℕ,∀ᶠ k:ℕ in atTop,∀ l:Filter (ℕ×ℕ),l.NeBot→l ≤ F.fuse→∃ f:Filter (ℕ×ℕ), f.NeBot∧ f ≤ l ∧∃ z':C.label d, S.project d z'=S.project d z ∧ ∀ᶠ i in f, Next.Rank.Spindle.paid C d k i.1 i.2 z' *C.S.a k ^ d ≤ β C k^L
variable (f:ℕ×ℕ→ℝ)
structure Outward (C:Family G)(F:Extraction.Order)(S:Table C.book)(P:DiffPlan S): Prop where
   paper d k : k≤d → ∀ (u: S.Field d→ₗ[ℂ]ℂ), (∀ j:ℕ,j < k→∀ hj:j≤ d,∀ v:S.Field j,u (P.rise hj v)=0)→∃ L:ℕ,∀ᶠ n:ℕ in atTop,∀ (l:Filter (ℕ×ℕ)),l.NeBot→ l≤ F.fuse→∀ (f:ℕ×ℕ→ C.label d) (z:C.label d)(q:ℝ),Tendsto f l (𝓝 z)→ (∀ᶠ i in l, Next.UVStress.quota C d n i.1 i.2 (f i) ≤ q) → ‖u (S.project d z)‖*C.S.a n^(d-k)≤β C n^L * q
structure Lanes (P:DiffPlan S):Prop extends Inward C F S, Outward C F S P
namespace Inward
variable (h:Inward C F S)
-- extend across finite menus where scaling projection independently arrived. Value retains physical Tok.
include h
lemma crew {I X:Type}[Fintype X]{l:Filter I}{q:X→I→ℕ} (p:X→ℕ)(v:∀ x,C.label (p x))(ht:∀ x,Tendsto (q x) l atTop): ∃ L:X→ℕ,∀ᶠ i in l,∀ ψ:Filter (ℕ×ℕ), ψ.NeBot→ ψ ≤ F.fuse→∃ φ:Filter (ℕ×ℕ),φ.NeBot∧ φ ≤ ψ ∧ ∃ z:∀ x,C.label (p x), (∀ x:X,S.project (p x) (z x)=S.project (p x) (v x)) ∧ ∀ᶠ j in φ,∀ x:X, Next.Rank.Spindle.paid C (p x) (q x i) j.1 j.2 (z x) * C.S.a (q x i)^(p x) ≤ β C (q x i)^(L x:ℕ):=by
   choose L HL using fun x=> h.allowed (p x) (v x)
   refine ⟨L,?_⟩; filter_upwards [eventually_all.mpr (fun x=>(ht x).eventually (HL x))] with i hi f hf hF
   let X0(x:X)(z:C.label (p x))(φ:Filter (ℕ×ℕ)):= (S.project (p x) z=S.project (p x) (v x)) ∧ ∀ᶠ j in φ, Next.Rank.Spindle.paid C (p x) (q x i) j.1 j.2 z*C.S.a (q x i)^(p x) ≤ β C (q x i)^L x
   suffices hA:∀ s:Finset X,∃ φ:Filter (ℕ×ℕ),φ.NeBot∧ φ≤ f∧ ∃ z:∀ x,C.label (p x),∀ x∈s,X0 x (z x) φ by
      obtain ⟨φ,hx,he,z,hZ⟩:=hA Finset.univ; refine ⟨φ,hx,he,z,fun x=>(hZ _ (Finset.mem_univ x)).1,eventually_all.mpr (fun x=>(hZ _ (Finset.mem_univ x)).2)⟩
   intro s; induction s using Finset.induction_on with
   | empty => exact ⟨_,hf,le_rfl,v,fun i hi=>False.elim (Finset.notMem_empty _ hi)⟩
   | insert x s hx ih=>
      obtain ⟨φ,hv,hq,V,hV⟩:=ih; obtain ⟨ψ,hψ,hp,z,hz,hK⟩ := hi x φ hv (hq.trans hF); refine ⟨ψ,hψ,hp.trans hq,Function.update V x z,fun t ht=>?_⟩
      obtain h|h:= Finset.mem_insert.mp ht
      · subst t; rw [Function.update_self x z V]; exact ⟨hz,hK⟩
      rw [Function.update_of_ne (by rintro rfl; contradiction : t≠x)]; exact ⟨(hV t h).1,(hV t h).2.filter_mono hp⟩
end Inward
end YM.OPE
