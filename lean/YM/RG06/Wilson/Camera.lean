import YM.RG06.Wilson.Easel
import YM.Source.Construction

/-!
# Ordered path coefficients at arbitrary finite demand

Default global link variables for a bare Wilson array (any lattice type with
positive axis steps, including Cover ℤ⁴ and Site n). We allow an arbitrary
linear log address stencil by taking `display` parameters, so paths and probes
can also be compiled directly in smaller tables on a support or in the coordinates
of `Orb.LinkP`. Later laws ensure restriction compatibility.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonCompiler
open Function Gauge Lattice GSeries Wilson
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {D : Type*} [AddCommGroup D] [One D]
variable {V : Type*}

abbrev DLink (D : Type*) := Edge (Four D)
abbrev LinkVar (G : Gauge) (D : Type*) := DLink D × G.ColorIndex
/-- Native stencil on log link inputs in variables V. -/
abbrev display (G : Gauge) (D V : Type*) := DLink D → Easel G V

def basic (G : Gauge) (D : Type*) : display G D (LinkVar G D) := fun e=> colorTube G (fun i=>MvPolynomial.X (e,i))

def access (G : Gauge) (u : Links D G.Color) (i : LinkVar G D) : ℝ := u i.1 i.2

section arbitrary
variable (K : display G D V) (q : V→ℝ) (u : Links D G.Color)

def Refines : Prop := ∀ e : DLink D, picture q (K e) = G.colorMat (u e)

omit [AddCommGroup D] [One D] in
lemma basic_refines : Refines (basic G D) (access G u) u := fun _e => colorTube_eval _ _ _ (fun _ => tone_X ..)

/-- Formal positive or negative link jet (negative uses `exp(-t*c)` at the
underlying positive edge). -/
def stepSeq (x : Four D) (s : Step) : Animation G V :=
    let T := K (s.used x)
    logRoll (if s.neg then -T else T)

def roll (u : Links D G.Color) (t : ℝ) : Links D G.El := fun l=> G.lieExp (t • u l)

theorem step_match (h : Refines K q u) (x : Four D) (s : Step) :
    Garnish 0 (fun r => G.mat (s.read (roll u r) x)) (soundtrack q (stepSeq K x s)) := by
  unfold roll stepSeq Step.read; cases e : s.neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact link_beat q _ _ (h _)
  simp_rw [← YM.Work.F03.exp_neg_color, ← smul_neg]
  apply link_beat; rw [map_neg,h (_, _),map_neg] -- h index is s.used, explicit e

def shoot (x : Four D) : Walk → Animation G V
 | []=> 1
 | s::w=> stepSeq K x s * shoot (x+s.vec) w

theorem shoot_match (h : Refines K q u) (x : Four D) (w : Walk) :
    Garnish 0 (fun r=> G.mat (travel (roll u r) x w)) (soundtrack q (shoot K x w)) := by
  induction w generalizing x with
  | nil => simp only [shoot,map_one,travel,G.mat_one]; exact Garnish.one ..
  | cons s w ih => simp_rw [shoot,map_mul,travel,G.mat_mul]; exact (step_match K q u h x s).mul (ih _)

/-- Color component linear read of the curvature map. -/
def paint (i : G.ColorIndex) : G.Mat →ₗ[ℝ] ℂ :=
   Complex.ofRealCLM.toLinearMap ∘ₗ (PiLp.projₗ 2 _ i) ∘ₗ G.projectColor ∘ₗ
    ((1/2:ℝ) • (LinearMap.id - (starL ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap.toLinearMap))

@[simp] theorem paint_curvature (i : G.ColorIndex) (u : G.El) : paint i (G.mat u) = (G.curvature u i : ℂ) := rfl -- or G.mat_inv not rfl?

def slotSeq (x : Four D) (s : RG.Slot) (i : G.ColorIndex) : PowerSeries (Pigment V) :=
  extract (paint i) (shoot K x (Work.F02.slotWalk s))


def vertex (x : Four D) (s : RG.Slot) (U : Links D G.El) := G.curvature (travel U x (Work.F02.slotWalk s))

theorem slot_cover (s : RG.Slot) (U : CoverConfig G) : s.eval U = vertex 0 s U := by
  unfold RG.Slot.eval vertex; rw [← G.curvature_conjugate]; congr 1
  rw [Work.F02.slotWalk,travel_append,travel_append,stop_append,square_stop,travel_reverse]; rfl

theorem slot_site (n : Side) (s : RG.Slot) (x : Site n) (U : Config G n) : s.atSite U x = vertex x s U := Work.F02.atSite_curvature ..

theorem slot_match (h : Refines K q u) (x : Four D) (s : RG.Slot) (i : G.ColorIndex):
    Garnish 0 (fun r => (vertex x s (roll u r) i : ℂ)) (develop q (slotSeq K x s i)) := by
  let L : G.Mat →ₗ[ℝ] ℂ := paint i
  let F (r : ℝ) := G.mat (travel (roll u r) x (Work.F02.slotWalk s))
  unfold vertex
  rw [show (fun r => _) = L ∘ F from funext (fun r=> Eq.symm (paint_curvature i (travel (roll u r) x (Work.F02.slotWalk s))))]
  exact extract_match q (G:=G) L (shoot_match K q u h x (Work.F02.slotWalk s)) -- colon dot
end arbitrary

open Source

/-- Bare positive link entry reading (analytic expansion of exp and conjugate on
real inputs, not a Laurent operation). Anchor and boundary handled by the
address `onCover` from microscopic edges to native edges. -/
def positive {X : Type*} (K : display G X V) {S : Finset Cover}
    (onCover : UsedEdges S → DLink X) (i : Index G S) : PowerSeries (Pigment V) :=
  frameP (logRoll (K (onCover i.1))) i.2.1 i.2.2.1 i.2.2.2

def locate {S : Finset Cover} (i : UsedEdges S) := i.val

theorem positive_cover_match (K : display G ℤ V) (v : V→ℝ) (u : Links ℤ G.Color) (h : Refines K v u) {S : Finset Cover}
    (i : Index G S) : Garnish 0 (fun t : ℝ => entry (roll u t) i) (develop v (positive K locate i)) := by
  exact frame_match v i.2.2.2 i.2.1 i.2.2.1 (link_beat (G:=G) v (K _) (u _) (h _))

def place {S : Finset Cover} {n : Side} (o : Site n) (i : UsedEdges S) : DLink (Per n) := (wrap n i.val.1+o,i.val.2)

theorem positive_site_match {n : Side} (K : display G (Per n) V) (v : V→ℝ) (u : Links (Per n) G.Color) (h : Refines K v u) {S : Finset Cover}
    (i : Index G S) (o : Site n) : Garnish 0 (fun t : ℝ => entry (expandAt o (roll u t)) i) (develop v (positive K (place o) i)) := by
  exact frame_match v i.2.2.2 i.2.1 i.2.2.1 (link_beat (G:=G) v (K _) (u _) (h _))
end YM.RG06.WilsonCompiler
