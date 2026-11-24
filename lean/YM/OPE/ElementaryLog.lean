import YM.OPE.Subpower
import YM.OPE.Log.Uniform
import YM.OPE.Log.Entrance

/-!
# Conditionally improving to logarithmic powers

No polynomial truncations of the action or marked moments are assumed.
Unfinished here without the matrix hypothesis. We use the opportunity to sharpen
the subpower results under the ticket in `Log/Measuring`. Keep the same prescription.
The strengthened families can in particular be chosen with all subpower conclusions,
and are the public choice anticipating use with the conditional result (still need that
ticket for THOSE families and adequate further joint estimates for factorization).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Log Next.Extract Dash Org Bid OS Ground Spec MergeProof
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}

structure Facilities (C:Family G)(F:Extraction.Order)(S:Table C.book) : Prop extends Services C F S where
    costlier : ∃ W r D, LogPackage C W r D
lemma Facilities.establishment (h:G.Simple){b:ℝ}(hb:0<b)(f:Extraction.Order) : ∃ C:Family G,C.path.levels.clock.kernel.penalty=b ∧ ∃ (t:Extraction.Order)(S:Table C.book), Facilities C (f.refine t) S ∧ Nonempty (Final C (f.refine t) S):=by
    obtain ⟨C,hB,hC,hM,hW,hS,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel_planned h hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    refine ⟨C,hB,g,T,⟨⟨hs,h,?_,A,L,R,E,hA⟩,hS⟩,Acme.glistens hC hA.clean.ready hA.clean.tilt p⟩; obtain ⟨w,z,Z,u⟩:= hS; exact ⟨w,z,Z,u.toPackage⟩

variable {C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Final C F S)
structure SingleLog (P:Prescription U.sector.derivatives) : Prop where
    coherent : P.Coherent
    terms (I:Type)[Fintype I] (p:I→ C.book.Token) (η M:ℝ) :
        0 < η → 0 ≤ M → ∀ i : Mode U.sector.derivatives,
          ∃ k:ℕ, ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(o:E4), WithinRoom r M η x o →
             (∀ u∈ (P.sheet i).support, Injective (beside (away x o) (bearing u))) ∧
                ‖P.ope i x p o‖ ≤ badge r^k * (r^i.fst / r^sigma p)
    horizons (I J:Type)[Fintype I][Fintype J] (p:I→ C.book.Token)(q:J→ C.book.Token) (η M c:ℝ):
        0 < η → 0 ≤ M → 0 < c → ∀ n : ℕ,
          ∃ k:ℕ, ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(y:J→ E4)(o:E4), WithinRoom r M η x o → ClearOf o y c →
             Injective (beside x y) ∧ Injective (beside (sole o) y) ∧
                Tested U P n x p o y q (badge r^k*(r^(n+1)/r^sigma p))

lemma first_log {P:Prescription U.sector.derivatives}(h:Facilities C F S)
     {𝓕:Filter (ℕ×ℕ)}[𝓕.NeBot] (he:𝓕≤ F.fuse)(hc: MatrixTicket (C:=C) S U.sector.derivatives 𝓕)(hP:P.Coherent): SingleLog U P:=by
     obtain ⟨W,r,D,L⟩:= h.costlier; exact ⟨hP,fun _ _ p _ _ hη hm => Log.terms U p h.toServices L he hc hP hm hη, fun _ _ _ _ p q _ _ _ hη hm hC n=> Log.horizons U p q n h.toServices L he hc hP hm hη hC⟩

/-- Public: A schedule poised to pay grouping at the costs for logarithmic analysis,
not conditional on the matrix estimate. Truly establishes common all-horizons
with the orders in `AllShapes`. -/
theorem prepared (G:Gauge)(h:G.Simple){b:ℝ}(hb:0<b)(f:Extraction.Order) : ∃ C:Family G,C.path.levels.clock.kernel.penalty=b∧ ∃ (t:Extraction.Order)(S:Table C.book), Facilities C (f.refine t) S ∧ ∃ (U:Final C (f.refine t) S) (P:Prescription U.sector.derivatives), AllShapes U P:=by
    obtain ⟨C,hC,g,S,hV,⟨U⟩⟩:= Facilities.establishment h hb f; obtain ⟨p,hp⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
    exact ⟨C,hC,g,S,hV,U,p,hV.toServices.everything U p hp⟩
end YM.OPE
