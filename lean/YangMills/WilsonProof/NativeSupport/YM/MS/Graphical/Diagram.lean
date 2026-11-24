import YM.MS.Graphical.Diagram
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Block
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land

/-!
# Bulk and one-mark scale diagrams

Represent an *ordered* Wick graph sector family here. E.g. use
`merge a b` for the use of ONE cross contraction of the connected diagrams
on the two sides. Includes all assignments of external and cut flags compatible
with this pattern. `close a` uses one more shell pair on the connected graph,
and increments actual dimension-loop count. Up to ties (integration endpoints)
the integrations are in the regions where the chosen line length is largest,
and recursively ordered sectors on its children. They're integrated by the
endpoint-continuation prescription with the cut (`scaleIntegral`), not by an
improper integral from a nonspecified side in D or by unspecified Wick sums.
This specifies the operands including how we handle overlaps: use *all* the
length resolutions in this grammar, whatever the other possibly divergent
subgraphs in other resolutions. Inside one resolution there are only nested
or disjoint subdiagrams. Use the sum including every retaining and
counterterm-replacing choice at these nodes (see `integrateRen`). No need to
budget separately for every split into terms with individual internal states.

Operational symmetry factors (often simpler than unordered-graph automorphism
factors):
* merge: ordered left/right components. Sum the allocation of external legs to
  the two sides, with Koszul signs via `bridgeForce` (`Lines`). Full line.
  For unmarked--unmarked this comes with 1/2 for summing over the two operands
  in order, as in exponential/connected Wick; use that **including** when
  both are the same. For a mark always choose *unmarked on the left* and no 1/2.
* close: ordered choice of **both** half-edges with pair propagator **halved**.
* These conventions, interpreting vertices by their canonical graded rows (from
  the exponent), mean no further overall or leg factorials. They specify the
  graph integrals themselves. There's no limit of a nonlinear path integral or
  prior claim of equivalence to other (e.g. graph-by-graph unsorted multi-scale)
  prescriptions in this definition. External lists are ordered and the sums in
  the graph are cutoff/analytically continued *as written*. Bulk nodes used in
  this grammar are connected diagrams with the conservation and extension rules
  in `Lines`. Only graphs connected to the mark contribute in `false` mode:
  the normalized (common source-free denominator) convention. Thus the
  normalization is by the graph rule, not a ratio of scalar amplitudes including
  infinite-volume δ's.

For explicit spinneys see `Spinneys`. Also, in addition to constructions by
sector grammar, later files give an un-sorting check at finite cut, with
line-count (radius) Wick enumeration; see e.g. `Centrifuge` and `ConnectCost`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open Lattice Cylinder Motif Literal Halo Outlook Mach
open scoped Topology ContDiff BigOperators Classical


namespace Diagram
variable {G : Gauge}

@[simp] def order : Diagram → ℕ
  | lit n => n
  | close g => order g
  | merge g h => order g + order h

/-- All unmarked vertices at positive coupling orders. No lower bound for a
marked vertex. We can of course leave zero amplitude terms in the sum. -/
def Valid : Diagram → Bool → Prop
  | lit n, b => b = true → 0<n
  | close g, b => g.Valid b
  | merge g h,b => g.Valid true ∧ h.Valid b

/-- Bound on **external field slots** of this entire family. Coupling order
is separately stored at the leaves, but vertex field ranks in this model
are always bounded by engineering height. -/
def rankBound (h : ℕ) : Diagram → Bool → ℤ
  | lit _, true => 4
  | lit _, false => h
  | close g, b => rankBound h g b - 2
  | merge g l,b => rankBound h g true + rankBound h l b - 2





/-- The forced coefficient in the length calculus: make the last shell (including
its momentum integration if a close), **after** inserting all lower subtractions,
but without its length integration. -/
def input (a : ℕ→ Mob G) (h : ℕ) : Diagram → Bool → Flats G
 | lit _, _ => 0
 | close g,b => closeForce (evaluate G a h g b).pages
 | merge g l,b => fee b • bridgeForce (evaluate G a h g true).pages (evaluate G a h l b).pages

def initialVertex (a : ℕ→ Mob G) : Diagram → Bool → Coat G
 | lit n, b => top G a b n
 | close _,_ | merge _ _, _ => 0

/-- Static admissibility for input vertices, including physical seeds from any of
the nominated optics (`mark_ok`); homogeneous with field and analytic caps. -/
abbrev VertexOK (b : Bool) (d : ℕ) (f : Mob G) := Count (fun _=> f) d ∧ Cap0 b 0 d (fun _=> f)
lemma pulse_ok (G : Gauge) (n : ℕ) : VertexOK true 4 (pulseX G n) :=
  ⟨(invest G n).born, bias (fun i=> (funded n G i).up) (give (invest G n)).2.2⟩

lemma mark_ok {A : Landau.Detect.Law G} (h k : ℕ) (T : Box (Mob G)) (he : Ele h k A T) (n : ℕ) :
    VertexOK false h ((linear (Mob G) T) n) := by
  obtain hp : Count0 (T n) h 0 := Present.pay (f:=fun z=>value (Mob G) z T)
      (K:=Count0.issueG G h 0) (show ∀ i:ℝ, value _ i T ∈ Count0.issueG G h 0 from
         (Gnome.GalleryG he.1).real') T (fun _=>rfl) n
  exact ⟨(he.grows n).born, bias (fun i=> (hp.tab i).up) (give (he.grows n)).2.2⟩

/-- The log-length flow for a contributing family. Unlike `Bob`, right hand
side here includes *only* the tagged sector forcing; the equation containing
`step0 G` is satisfied after summing over families. -/
abbrev Runs (b : Bool) (h : ℕ) (r : ℤ) (I : Flats G) (f : Coat G) (T : SectorFamily G) : Prop :=
  Joint h I T.pages f T.ct ∧ ClockD b 0 r T.pages ∧ Cap0 b 0 r T.ct

variable {V W : SectorFamily G} {a : ℕ→Mob G} {b : Bool} {h k : ℕ}
    {q r : ℤ} {f : Coat G} {I : Flats G}

lemma expandRuns (V : SectorFamily G) (hv : Runs b h r I f V) (h' : r ≤ q) : Runs b h q I f V :=
   ⟨hv.1, clockTrans hv.2.1 h', hv.2.2.collects h'⟩

lemma reduce_bool (hx : Runs true h r I f V) : Runs b h r I f V := by
  cases b; swap; · exact hx
  exact ⟨ hx.1, fun i =>⟨(hx.2.1 i).fine.tire,(hx.2.1 i).cap⟩,⟨hx.2.2.fine.tire,hx.2.2.cap⟩ ⟩

lemma certify_vertex {X : Mob G} (ht : VertexOK b h X) :
    Runs b h h (0:Flats G) (fun _=> X) ⟨Finsupp.single 0 (fun _=>X),0⟩ := by
  exact ⟨joint_static ht.1 (Live.stays (give (K:=X) ⟨ht.1,_,ht.2⟩).1), Cap0.heap.single ht.2 0, Cap0.zero⟩

lemma certify_join {g} {J} (hx : Runs true 4 r I f V) (ht : Runs b h q J g W) :
  Coal b h 0 (r+q-2) (fee b • bridgeForce V.pages W.pages) := by
  obtain ⟨hw,h,hC⟩:= reduce_bool (b := b) hx; obtain ⟨hv,hH,hX⟩:= ht
  refine glazer (bridge_coal h ⟨⟨_,h⟩,hw.toll,⟨_,hw.sip⟩⟩ hH ⟨⟨_,hH⟩,hv.toll,⟨_,hv.sip⟩⟩) _ ?_
  cases b <;> simp [fee]

/-- Each sector family separately solves flow with the forcing `input`, which in
turn has the conditions for UV integration (`Coal`). This verifies that the integrals
and principal-part extractions in the definitions make sense (for the germ).
Later `Bob` will hold on the relevant *sum* of these (`wide_ladder` in `Ladder`). -/
theorem ordered (a : ℕ → Mob G) (hv : ∀ i, VertexOK false h (a i)) (g : Diagram) (b : Bool) :
    Coal b (dimTarget h b) 0 (rankBound h g b) (input a h g b) ∧
    Runs b (dimTarget h b) (rankBound h g b)
      (input a h g b) (initialVertex a g b) (evaluate G a h g b) := by
  induction g generalizing b with
  | lit n => cases b
             · rw [input,evaluate,rankBound,initialVertex]; exact ⟨coal_zero ..,certify_vertex (hv _)⟩
             rw [input,evaluate,rankBound,initialVertex]; exact ⟨coal_zero ..,certify_vertex (pulse_ok G _)⟩
  | merge g k ih ih' =>
     obtain he := certify_join (b:=b) (ih true |>.2) ( (ih' b).2 )
     rw [input,rankBound,initialVertex,evaluate]; exact ⟨ he,block he ⟩
  | close g ih=>
     obtain ⟨hx,h,hV⟩:=(ih b).2; rw [rankBound,input,initialVertex,evaluate]
     obtain he := close_coal h hx.toll
     exact ⟨he,block he⟩

/-- On the germ, the loop integration domain conditions when `g` is used in a
further close as renormalized input pages. (See `cycle_integrals_exist`.) -/
theorem cycles_integrable (a : ℕ→ Mob G) (hv : ∀ i, VertexOK false h (a i)) (g : Diagram) (b : Bool) :
   let V := evaluate G a h g b
   ∀ᶠ z in dotty, z∈Town ∧ ∀ ℓ : ℕ, Form0 false (V.pages ℓ z) := by
  intro V; exact (show ∀ᶠ z in dotty, z∈Town from high0).and (Moony.sunup (all0 (clockMoon (ordered a hv g b).2.2.1)))


theorem expand_order (h : ℕ) (v : Diagram) (hv : Valid v b) :
    rankBound h v b ≤ (rankRoom h b (order v) : ℤ) := by
  induction v generalizing b with
  | lit n =>
    cases b; swap
    · have hN := hv rfl
      rw [rankBound,order,rankRoom]; push_cast; simp only [↓reduceIte]; omega
    rw [rankBound,order,rankRoom]; push_cast;  omega
  | merge v w ih ih'=>
    obtain ht := ih (b:=true) hv.1
    obtain he:= ih' (b:=b) hv.2
    rw [rankBound,order]; unfold rankRoom at *; push_cast at *; simp only [↓reduceIte] at *; omega
  | close v ih =>
    rw [rankBound, order]; obtain h:= ih (show v.Valid b from hv); omega

end Diagram
end YM.MS.Graphical
