import YM.MS.LandauMatch
import YM.Gauge.Casimir
/-!
# Feasible symmetry tests on the vertices

Use actual gauge group (`G`, with its original color conventions) and invariance
including disconnected components. Rank-supported, ghost-channel, real and H
(signed permutations) are pointwise kernel properties. Transport under the flow
and operations still to be proved. Nonbulk vertices can use only color
invariance. No truncated cohomology or gauge fixing in these tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Function Filter Set LogTime Plane Real Koszul Wire
open scoped Topology ContDiff

namespace Plane
variable {A P : Type} [AddCommGroup P] {b : Bool}
-- `Course` defined with NormedAddCommGroup; generalize? for grid proof later rely Conserved.
end Plane
namespace Landau
variable {D P : Type} {G : Gauge}
variable (G) in abbrev Branch (D : Type):= Leg D G.ColorIndex
abbrev Note (G : Gauge) (D P : Type) := Mode (Branch G D) P
abbrev Score (G : Gauge) (D P:Type) := Row (Branch G D) P ℂ

def ghostChannel (i:Atom D) : ℤ:= match i with
| (none,false)=>1
| (none,true)=> -2
| (some _,false)=>0
| (some _,true)=> -1
abbrev ghostNo (i:Branch G D) := ghostChannel i.1

def weight (g:G.El) (i j : G.ColorIndex) := G.adjoint g ((EuclideanSpace.basisFun G.ColorIndex ℝ) i) j
-- Evaluate coefficient on Adj-rotated external arguments.
def solo (g:G.El) (w : Legs (Note G D P)) (F: Score G D P): ℂ := match w with
 | []=> F []
 | ((i,k),p)::l=> ∑ q:G.ColorIndex, (weight g k q:ℂ)*solo g l (fun l=> F (((i,q),p)::l))
-- Rank support; color including midpoint spacetime sign flips
variable {b : Bool}
-- inversion and test reality
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
def invertMom : Legs (Note G D P) → Legs (Note G D P) := fun w=> w.map (fun i=> (i.1,-i.2))
omit [NormedSpace ℝ P] in
lemma net_invert (w : Legs (Note G D P)): net (invertMom w)= - net w:= by induction w with | nil=> simp [invertMom,net] | cons a w ih => unfold invertMom at *; simp only [List.map_cons,net_cons, ih, neg_add]

structure Solid (b : Bool) (F : Score G D P) (g : ℤ): Prop where
   symm (l) i k r (h:Course b (l++i::k::r)): F (l++i::k::r)=cross (parity i.1) (parity k.1)*F (l++k::i::r)
   ghost (w) (h:Course b w): fieldDim ghostNo w≠g → F w=0
   color (w) (h:Course b w) a: solo a w F= F w
   real' (w) (h:Course b w): F (invertMom w)= star (F w)
-- pure scalar kernel tensor. Use Axis (raw H). Later full O(D) tests for dimensions.
abbrev Lane4 (G : Gauge):= Note G Axis (Momentum Axis)

-- permutation of midpoint wave fields applies coefficient sign on vectors and antifield vectors only
def permute (k:Signed) (i:Lane4 G): Lane4 G:= ((((i.1.1.1.map k.perm,i.1.1.2),i.1.2)), k.act i.2)
def negateField (k:Signed) (i:Lane4 G) : ℂ:= match i.1.1.1 with
    | none=>1
    | some i=> cross (k.flip i) true

def SignedScope (b:Bool) (F:Score G Axis (Momentum Axis)) := ∀ k:Signed, ∀ w, Course b w→ (w.map (negateField k)).prod* F (w.map (permute k))=F w

/-! Tint vector real action via multilinear polarization will use `EuclideanSpace.basisFun`. -/
variable (G) in abbrev eb (i:G.ColorIndex) := (EuclideanSpace.basisFun G.ColorIndex ℝ) i
lemma real_color (k : G.ColorIndex) (f : G.Color): ((EuclideanSpace.basisFun G.ColorIndex ℝ).repr f) k=f k:= by simp
lemma color_sum (f : G.Color) : ∑ i:G.ColorIndex, f i • eb G i=f:= by
    have ht:= OrthonormalBasis.sum_repr (EuclideanSpace.basisFun G.ColorIndex ℝ) f; simpa [real_color] using ht
lemma tint (i j : G.ColorIndex) (b : G.El) : G.adjoint b (eb G i) j = weight b i j:= rfl

end Landau
end YM.MS
