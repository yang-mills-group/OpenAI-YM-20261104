import YM.RG06.Wilson.Camera

/-!
# Local stencil film (`g` coefficients at the bare input)

One `Formula` per Label via the actual common `Family.localSection`. This is the
unmasked germ before slot divisions or engineering extraction. The top stencil
compiler is independent of any derivatives, Wick expectations or the actual
readout; the identities concern derivatives of the actual stencil as a cylinder
on exponential link arrays, not correlation claims. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonCompiler
open GSeries Function Source Wilson Lattice RG Labels
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {D V : Type*}
variable {m d : ℕ} {F : Frame G d} {S : Finset Cover}

/-- Scalar polynomial at the chart, coefficients via the algebra map. -/
def compile {I : Type*} (v : I → PowerSeries (Pigment V)) :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp (MvPolynomial.C (R:=ℂ))) v

@[simp] lemma quoted (z : ℂ) (u : V → ℝ) : develop u (PowerSeries.C (MvPolynomial.C z)) = PowerSeries.C z := by
  unfold develop; rw [PowerSeries.map_C,tone_C]

theorem compile_developed {I : Type*} (p : MvPolynomial I ℂ) (a : V→ℝ)
    (v : I → PowerSeries (Pigment V)) :
    develop a (compile v p) = MvPolynomial.eval₂Hom PowerSeries.C (fun i=> develop a (v i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => unfold compile; rw [MvPolynomial.eval₂Hom_C,RingHom.comp_apply,MvPolynomial.eval₂Hom_C, quoted]
  | add p q hp hq => rw [map_add,map_add,hp,hq,map_add]
  | mul_X p i hp =>
    rw [map_mul,map_mul,hp,map_mul, compile, MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_X']

lemma compile_mark {I : Type*} (p : MvPolynomial I ℂ) (a : V→ℝ) (t : ℝ) (f : I → ℝ → ℂ)
    (v : I → PowerSeries (Pigment V)) (h : ∀ i, Garnish t (f i) (develop a (v i))) :
    Garnish t (fun r => MvPolynomial.aeval (fun i=> f i r) p) (develop a (compile v p)) := by
  rw [compile_developed]; apply lift_mark; exact h

/-- Entire unnormalized stencil, with arbitrary effective link addresses. -/
def film (p : Source.Formula G S) (K : display G D V) (l : UsedEdges S → DLink D) :
    PowerSeries (Pigment V) := compile (positive K l) p

def top (X : SectionData F) (v : F.Coeff) (K : display G D V) (l : UsedEdges X.stencil → DLink D) :=
  film (X.evalC v) K l

def cover (p : Formula G S) (K : display G ℤ V) := film p K locate

def atSite {n : Side} (p : Formula G S) (K : display G (Per n) V) (x : Site n) := film p K (place x)

theorem cover_formula (p : Formula G S) (K : display G ℤ V) (a : V→ℝ) (u : Links ℤ G.Color)
    (h : Refines K a u) :
    Garnish 0 (fun r=> MvPolynomial.aeval (entry (roll u r)) p) (develop a (cover p K)) :=
  compile_mark p a 0 (fun i r=> entry (roll u r) i) (positive K locate) (positive_cover_match K a u h)

theorem site_formula {n : Side} (p : Formula G S) (K : display G (Per n) V) (a : V → ℝ) (u : Links (Per n) G.Color)
    (h : Refines K a u) (x : Site n) :
    Garnish 0 (fun r=> MvPolynomial.aeval (entry (expandAt x (roll u r))) p) (develop a (atSite p K x)) :=
  compile_mark p a 0 (fun i r=> entry (expandAt x (roll u r)) i) (positive K (place x)) (fun i=>positive_site_match K a u h i x)

/-- Read a pose in transported slots by the same compiler, oriented path reads. -/
def frameFilm (p : Bid.Pose G m) (B : Fin m → Slot) [AddCommGroup D] [One D] (x : Four D) (K : display G D V) := compile
    (fun i=> slotSeq K x (B i.1) i.2) p

theorem pose_formula [AddCommGroup D] [One D] (K : display G D V) (a : V→ℝ)
    (u : Links D G.Color) (h : Refines K a u) (x : Four D) (p : Bid.Pose G m)
    (B : Fin m → Slot) :
    Garnish 0 (fun r=> Bid.lumin p (fun i : Fin m => vertex x (B i) (roll u r))) (develop a (frameFilm p B x K)) :=
  compile_mark p a 0 (fun i r=> (vertex x (B i.1) (roll u r) i.2 : ℂ)) _ (fun i => slot_match K a u h x (B i.1) i.2)

lemma pose_cover (K : display G ℤ V) (a : V → ℝ) (u : Links ℤ G.Color) (h : Refines K a u) (p : Bid.Pose G m)
    (B : Fin m → Slot) :
    Garnish 0 (fun r => Bid.lumin p (Bid.mapped B (roll u r))) (develop a (frameFilm p B (0:Cover) K)) := by
  refine Eq.mp ?_ (pose_formula K a u h 0 p B)
  unfold Bid.mapped
  simp_rw [slot_cover]

lemma pose_site {n : Side} (K : display G (Per n) V) (a : V → ℝ) (u : Links (Per n) G.Color) (x : Site n)
    (h : Refines K a u) (p : Bid.Pose G m) (B : Fin m → Slot):
    Garnish 0 (fun r => Bid.lumin p (Bid.mapped B (expandAt x (roll u r)))) (develop a (frameFilm p B x K)) := by
  have he r : Bid.mapped B (expandAt x (roll u r)) = fun i=> vertex x (B i) (roll u r) :=
    funext fun i=> slot_site ..
  simp_rw [he]; exact pose_formula K a u h x p B

/-! Cylinder on global link coordinates. The polynomial itself, not just its
point readings, is pinned by link readings for all arrays, even when the
index type is infinite. -/
lemma pigment_ext {p q : Pigment V} (h : ∀ a : V → ℝ, tone a p = tone a q) : p=q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun x : ℝ => (x : ℂ))) fun _ =>
    Set.infinite_range_of_injective Complex.ofReal_injective
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  rw [show x = fun i=> (y i:ℂ) from funext fun i=> (hy i).symm]
  exact h y

theorem folio_ext {p q : PowerSeries (Pigment V)} (h : ∀ a : V → ℝ, develop a p=develop a q) : p=q := by
  ext1 k; refine pigment_ext fun a=>?_
  exact (Eq.symm (develop_coeff ..)).trans ((congrArg (fun z=>PowerSeries.coeff k z) (h a)).trans (develop_coeff ..))

def peeling (G : Gauge) (a : LinkVar G D→ℝ) : Links D G.Color := fun i=> WithLp.toLp 2 (fun j=> a (i,j))

@[simp] lemma access_peel (a : LinkVar G D→ℝ) : access G (peeling G a) = a := by funext x; rfl

/-- Exact global input film of the horizon stencil. Distinct from its
normalized cutoff field `C.O`. -/
def markTop (C : Family G) (d : ℕ) (x : C.label d) : PowerSeries (Pigment (LinkVar G ℤ)) :=
  cover ((C.localSection d).evalC x) (basic G ℤ)

def markSite {n : Side} (C : Family G) (d : ℕ) (x : C.label d) (o : Site n) :
    PowerSeries (Pigment (LinkVar G (Per n))) := atSite ((C.localSection d).evalC x) (basic G (Per n)) o

/-- Coupling coefficients of the top insertion, exactly, unnormalized. -/
theorem gasket (C : Family G) (d : ℕ) (x : C.label d) (A : Links ℤ G.Color) :
    Garnish 0 (fun t => (C.localSection d).evaluate x (roll A t)) (develop (access G A) (markTop C d x)) := by
  exact cover_formula ((C.localSection d).evalC x) (basic G ℤ) (access G A) A (basic_refines _)

theorem orbit {n : Side} (C : Family G) (d : ℕ) (x : C.label d) (o : Site n) (A : Links (Per n) G.Color) :
    Garnish 0 (fun t => (C.localSection d).places x o (roll A t)) (develop (access G A) (markSite C d x o)) := by
  exact site_formula ((C.localSection d).evalC x) (basic G (Per n)) (access G A) A (basic_refines _) o

/-- Congruence of `Formula` and `Pose` readings on the cover implies congruence
of both global and periodic films, even on wrapping supports. This means we can
use `pop` without changing canonical coefficient data, and use path-length-based
bounds where natural. -/
theorem formula_cover_eq (p : Formula G S) (w : Bid.Pose G m) (B : Fin m→Slot)
    (h : ∀ U : CoverConfig G, MvPolynomial.aeval (entry U) p=Bid.lumin w (Bid.mapped B U)) :
    cover p (basic G ℤ)=frameFilm w B (0:Cover) (basic G ℤ) := by
  refine folio_ext fun a => ?_
  rw [← access_peel a]; let A := peeling G a
  exact (cover_formula p (basic G ℤ) _ A (basic_refines _)).series.trans
    ((congrArg (fun f : ℝ→ℂ => assembler 0 f) (funext fun t=> h (roll A t))).trans
      (pose_cover (basic G ℤ) (access G A) A (basic_refines _) w B).series.symm)

theorem formula_site_eq {n : Side} (p : Formula G S) (w : Bid.Pose G m) (B : Fin m→Slot)
    (h : ∀ U : CoverConfig G, MvPolynomial.aeval (entry U) p=Bid.lumin w (Bid.mapped B U)) (o : Site n):
    atSite p (basic G (Per n)) o=frameFilm w B o (basic G (Per n)) := by
  refine folio_ext fun a => ?_
  rw [← access_peel a]; let A := peeling G a
  exact (site_formula p (basic G (Per n)) _ A (basic_refines _) o).series.trans
    ((congrArg (fun f : ℝ→ℂ=>assembler 0 f) (funext fun t=>h (expandAt o (roll A t)))).trans
      (pose_site (basic G (Per n)) (access G A) A o (basic_refines _) w B).series.symm)
end YM.RG06.WilsonCompiler
