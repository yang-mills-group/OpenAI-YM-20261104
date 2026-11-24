import YM.AllOrder.Leading.Solve
import YM.AllOrder.Construction.Bridge
import YM.AllOrder.Leading.Phases
import YM.X.Stage.T1

/-!
# First end-to-end (leading stage only!)

CP1. ν fixed regulator trajectory of PositionX (`q`); phases see one Reader
and one actual family of frames normalized by exactly its nested D, not an
independent choice nor at sparse scales. Includes actual stress generator and
$d2$ trace readout in those POSITIONED frames (Peano normalization). Does *not*
 transfer trace's O(g^4) budget yet. `glo P'` and the trace scheme stay named
 separately. Match here only coupling-independent order 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open OPE OPE.Orbits MeasureTheory PositionX PositionX.Bend Leading
open scoped BigOperators Topology Classical ContDiff
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

structure FirstMatch (F : Final C f S) (h : G.Simple)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (g : ℝ → ℝ) (U : ℝ → FamilyFrame S) (K : PositionX.Bare.Shop C.labels)
    (c : ℝ) (T : PositionX.Bend.Booth c C.labels) : Prop where
  aligned : Aligned F g U
  table_positions d : ∀ᶠ r in trail, (PositionX.nested C.labels h K d).D (bankAt F.room.kernel (U r d) r) =
    (PositionX.nested C.labels h K d).D (pureBank C.labels d)
  services : OPE.Services C f S
  charts : K.H=C.params -- incl holonomies of actual stencils
  stencils : K.S=C.localSection
  t1 (q : ℕ+) (hq : 1<q.val) : PositionX.Knocker h T q hq K
  independent_nest (q : ℕ+)(hq : 1<q.val)(d e:ℕ)(hd : d ≤ e) :
    ∀ᶠ i:ℕ in atTop, pulls (up C.labels hd) ∘ renormal K q h T i e = renormal K q h T i d
  exact_ope : Foundation F R ∧ Nesting.Uniform F R
  -- regulator limit identified with free leading in the scheme
  zero (q : ℕ+)(hq : 1<q.val)(d n:ℕ)(v:Fin n→(Bel C.book).Field d)(p:Test n) :
     Tendsto (fun i:ℕ => renormal K q h T i d 0 n p v) atTop (𝓝 ((pureBank C.labels d) n p v))
  -- the corresponding genuine leading match
  matches_zero (d n:ℕ)(v:Fin n → (Bel C.book).Field d)(p:Test n)(s : ℝ→Viewers F): Tendsto
    (fun r => p.applyTo (phaseRead F U (d:=fun _=>d) v r (s r))) trail (𝓝 ((pureBank C.labels d) n p v))
  -- exact output-scalar match via phase comparison: at all lengths
  scalar (I : Type) [Fintype I] (d : I→ℕ) (v : (i:I)→ (Bel C.book).Field (d i)) (M η : ℝ)(hη:0<η) :
    ∀ ε : ℝ,0<ε→ ∀ᶠ r in trail, ∀ x∈ Short.plate I M η,∀ o q,
      ‖moments F U v r x o q - Levy.freeSlots v x‖ < ε ∧ ‖scalarChannel F R U v r x o-Levy.freeSlots v x‖<ε

/-- Wilson schedule/final carrying the exact frame, leading matching and
 OPE/nonzero-trace. Entry on the same construction. `S` seed and Final in A,
not claiming other components about separately packaged FullVolume results.
`aligned` charges in the still-leading coupling convention `glo`. -/
theorem first_match (h : G.Simple) (b : ℝ) (hb : 0<b) (p : Extraction.Order) :
    ∃ (C : Family G), C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧
    ∃ (q : Extraction.Order) (S : Table C.book) (A : PertExtension.Actual C (p.refine q) S),
      SupportsMatching.{u} h A.F ∧
       (∃ (H : (Bel C.book).Hierarchy) (Z : Arch C) (l : Ultrafilter (ℕ × ℕ))
           (P P' : ℝ → Spin.change S 4) (χ : E4 → ℝ) (κ d e : ℝ → ℝ) (K : PositionX.Bare.Shop C.labels)
           (c : ℝ) (T : PositionX.Bend.Booth c C.labels) (U : ℝ → FamilyFrame S)
           (R : Reader A.F.sector.derivatives A.F.sector.turns A.F.room.kernel.spin),
         Trace.Target.XScheme A.F h H l P P' χ ∧
         Trace.Target.FieldComparison A.F H Z P P' κ d e ∧ Bliss A.F l Z H ∧
         FirstMatch A.F h R (Sundial.glo P') U K c T) := by
    obtain ⟨C,hB,hW,q,S,A,hF⟩ := matching_data.{u} h b hb p
    let F:= A.F
    have hp := hF.services
    obtain ⟨R,hP⟩:= hF.ope
    obtain ⟨H,Z,l,hV,⟨χ,P,P',hS⟩,hQ⟩ := hF.result.stress
    obtain ⟨κ,d,e,he⟩ := hQ χ P P' hS
    obtain ⟨U,hU⟩ := aligned_exists h hV he.coupling
    let K : PositionX.Bare.Shop C.labels := ⟨C.params, C.localSection,A.F.room.cutoff.sections,hF.pop⟩
    obtain ⟨c,T,hx⟩ := can_booth K h
    obtain ⟨ht,hL⟩:= solves_position_in_frame hU K h
    refine ⟨C,hB,hW,q,S,A,hF,H,Z,l,P,P',χ,κ,d,e,K,c,T,_,R,hS,he,hV,ht,hL,hp,rfl,rfl,
       fun q hq=>PositionX.lit h T q hq K (hx q hq).2, fun q hq _ _=> Bend.θ_up K q h T hq,hP,
       fun q hq d n v p => leading_edge K q h T hq (⟨n,v,p⟩:Pert.Position.Section C.labels d),
       ?_, fun _ _ _ v _ _ hη ε he=> Leading.plate R v ht hp h hη he⟩
    intro d n v p s
    exact test_tend R (d:=fun _=>d) v ht hp h p s
end YM.AllOrder
