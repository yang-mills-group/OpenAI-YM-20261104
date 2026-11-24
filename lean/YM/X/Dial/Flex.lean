import YM.X.Grow.Tele
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
/-!
Hyperoctahedral signed H: actions on Cover polynomials of potential legs and *periodically deployed* ones. No covariance of arbitrary finite center window assumed. This will allow averaging at the differential budget level.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Dial
open Lattice Wilson Next.Rank Normal MvPolynomial Function Stems -- syntax
open PertExtension LatticePT Filter MeasureTheory Set Metric
open scoped Topology ContDiff BigOperators Pointwise
variable {R:Type*} [AddCommGroup R][One R]{G:Gauge}{n:Side}(s:Signed)
abbrev Stem(R:Type*) := Edge (Four R)
abbrev Deck(R:Type*)(G:Gauge):= Stem R × G.ColorIndex
def landing (e:Stem R):Stem R:=((posDir e.2).rotate s).used (s.act e.1)
def digit (i:Axis):ℝ:= if s.flip i then -1 else 1
def loc (x:Deck R G):Deck R G:= (landing s x.1,x.2)
def reserve (x:Deck R G) : Deck R G→₀ ℂ := Finsupp.single (loc s x) (digit s x.1.2 :ℂ)
def relay : poly (Deck R G) →ₐ[ℂ] poly (Deck R G):= exchange (reserve s)
omit [AddCommGroup R][One R] in
lemma digit_nonzero(i:Axis): digit s i≠0:= by unfold digit;split_ifs<;>norm_num
def Lbrush (s:Signed): (Stem R→G.Color) →ₗ[ℝ] Stem R→G.Color:= LinearMap.pi (fun i=> digit s i.2 • LinearMap.proj (landing s i))
lemma Lbrush_point (A:Stem R→G.Color) (i:Stem R): Lbrush s A i= digit s i.2 • A (landing s i):= rfl
lemma relay_point (i:Deck R G): relay s (MvPolynomial.X i)= (digit s i.1.2:ℂ) • MvPolynomial.X (loc s i):= by rw [relay,exchange_x,glyph,reserve,Finsupp.linearCombination_single]
def readD (A:Stem R→G.Color): poly (Deck R G)→ₐ[ℂ] ℂ:= MvPolynomial.aeval fun i=> (A i.1 i.2 :ℂ)
lemma read_relay (A:Stem R→G.Color)(p): readD A (relay s p)= readD (Lbrush s A) p:= by
    apply DFunLike.congr_fun (f:=(readD A).comp (relay s)); ext1 i; rw [AlgHom.comp_apply,relay_point,map_smul]; simp [readD,Lbrush_point,loc]
lemma read_snap (p:Curly G)(A:Brush G): snap A (relay s p)= snap (Lbrush s A) p:= read_relay s A _
lemma rotate_false (i:Stem R)(h:s.flip i.2=false): landing s i=(s.act i.1,s.perm i.2) := by unfold landing; simp [Step.used,Step.rotate,posDir,h]
lemma rotate_true (i:Stem R)(h:s.flip i.2=true): landing s i=(s.act i.1-step (s.perm i.2),s.perm i.2) := by unfold landing; simp [Step.used,Step.rotate,posDir,h]
lemma land_exp (A:Stem R→ G.Color): (pull s 0 (G.lieExp ∘ A))=(G.lieExp ∘ Lbrush s A):= by
    funext i; rw [comp_apply, Lbrush_point, pull,Step.read,digit]; simp only [posDir,Step.rotate, Bool.false_xor,affine,add_zero]; cases h:s.flip i.2
    · rw [rotate_false s i h]; simp [Step.used]
    rw [rotate_true s i h]; simp [Step.used, Work.F03.exp_neg_color]
lemma proposed (z:Site n)(p:Curly G) : hairAt (s.act z) (relay s p) = relay (R:=Per n) s (hairAt z p):= by
    apply DFunLike.congr_fun (f:=(hairAt (s.act z)).comp (relay s)) (g:=(relay s).comp (hairAt z)); ext1 i
    rw [AlgHom.comp_apply,AlgHom.comp_apply,hairAt,hairAt,rename_X,relay_point,relay_point,map_smul,rename_X]
    cases h : s.flip i.1.2 <;> {unfold loc; rw [show (place z i).1.2=i.1.2 from rfl]; simp [landing,Stems.place,west, h,Step.used,Step.rotate,posDir] <;> congr 3 <;> abel} -- rw inside landing doesn't see. edit
end YM.PositionX.Dial
