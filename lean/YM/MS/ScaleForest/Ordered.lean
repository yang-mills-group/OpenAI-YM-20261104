import YM.MS.ScaleForest.Distribute

/-!
# Ordered contraction histories: vertex, loop and bridge graphs

This type indexes graph SUMS, not individual isomorphism classes with
symmetry divisors. For example, two parallel lines can be made by `loop` of
a `bridge` and the actual integral does both assignments when appropriate.
A bridge attaches ANY free leg from either of two components (`scatter` and
the signed cross), and a loop attaches ANY two of the free legs (including at
the same vertex, without excluding overlap topologies).
There is no disjoint-or-nested restriction on the GRAPHS. At no point in a
`GraphSum` with `b=false` is the mark itself an internal Wick half-edge.

Boolean flag `b=true` means no insertion present. At a `loop` both the
parent and child have the same flag, and at a `bridge` the LEFT is always
unmarked and the right carries the flag. Use `factor b` at a bridge: an
ordered pair contribution to the *connected* log expansion (`1/2` of the Wick
cross), or the linear-in-source variation (keep the WHOLE cross with the mark
in the right component). This is an ordered-scale Feynman convention; use
the recursion directly as definition, e.g., don't take an unrooted formula
with these factors, and use the indicated scale integration order AND UV
limit order. Admissible subtractions in this convention are specified in the
recursion, not e.g. the product of pole parts of all divergent sub-integrals
without regard to their overlap. For an overarching order calculation there
will be a **sum** over these ordered histories. See also `Inlay`/`Installation`,
`Lifelong`/`Finnacle` and `ClockOrders` for the corresponding Wick expansion
with pole vertices already installed and the result about permitting all
edge topology/scale orders.

`instructions` records the shell integrand *after* feeding it the renormalized
child components, and the classical part (if just a bare vertex), Laurent
series and pole with a `Result` record. We'll prove this recursion computes the forest
sum over admissible subtractions, including in-shell pole insertions on proper
subgraphs (`Quotients.lean`). Here we establish that all its operations work and
that this actual calculation satisfies a filed `Joint`. In particular, the
pole table will be CALCULATED by our graphs. No `MS_Data` cost hypotheses on
them.

All geometry including canonical continuation of the mark's source slots is
carried by the inputs. These constructors are general enough to also select
some specific families (e.g. currents with only one kind of half-line).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave
open scoped Topology ContDiff

structure LineRule (G : Gauge) where
  half : Rip G
  ok : HalfKernel half

def fullShell (G : Gauge) : LineRule G := ⟨A0 G 0, wick G⟩

/-- One bare vertex, rank (number of external dynamical legs) fixed. -/
structure LocalVertex (G : Gauge) (b : Bool) (h : ℕ) where
  rank : ℤ
  symbol : Mob G
  scaling : Home symbol h
  cap : Cap0 b 0 rank (fun _ => symbol)
  slots : Goods rank symbol

/-- The ordered sum family with given vertices and specified Wick line
insertions. Use `true,4` for unmarked sector; `false,h` for a marked row of
engineering grade `h`. -/
inductive GraphSum (G : Gauge) : Bool → ℕ → Type where
  | vertex {b : Bool} {h : ℕ} : LocalVertex G b h → GraphSum G b h
  | loop {b : Bool} {h : ℕ} : LineRule G → GraphSum G b h → GraphSum G b h
  | bridge {b : Bool} {h : ℕ} : LineRule G → GraphSum G true 4 → GraphSum G b h → GraphSum G b h

structure Result (G : Gauge) where
  /-- derivative kernel at unit length, pages. -/
  force : Flats G
  classicalTerm : Coat G
  /-- the scale integral with child counterterms included -/
  prep : Flats G
  pole : Coat G

def Result.renorm {G : Gauge} (R : Result G) : Flats G := R.prep + collapsed R.pole

variable {G : Gauge} {b : Bool} {h : ℕ} {r : ℤ}

namespace GraphSum

def slots : {b : Bool} → {h : ℕ} → GraphSum G b h → ℤ
| _, _, .vertex V => V.rank
| _, _, .loop _ F => slots F - 2
| _, _, .bridge _ F H => slots F + slots H - 2

def factor (b : Bool) : ℝ := if b then 2⁻¹ else 1

/-- After sewing a new edge, integrate scales and assign the *local*
subtraction to the result. -/
def sew (h : ℕ) (X : Flats G) : Result G :=
  let R := integratePages h X
  ⟨X,0,R,counterterm R⟩

def connect (b : Bool) (U : LineRule G) (X Y : Flats G) : Flats G :=
  (factor b : ℂ) • bridgePages U.half X Y

def instructions : {b : Bool} → {h : ℕ} → GraphSum G b h → Result G
| _, _, .vertex V => ⟨0, fun _ => V.symbol, collapsed (fun _ => V.symbol), 0⟩
| _, h, .loop U X => sew h (closePages U.half (instructions X).renorm)
| b, h, .bridge U X Y => sew h (connect b U (instructions X).renorm (instructions Y).renorm)

structure Good (b : Bool) (r : ℤ) (h : ℕ) (X : Result G) : Prop where
  force : Coal b h 0 r X.force
  before : Sewable b r h X.classicalTerm X.prep
  poleShape : Cap0 b 0 r X.pole
  after : Joint h X.force X.renorm X.classicalTerm X.pole
  legs_in : OfRank r X.force
  legs_pre : OfRank r X.prep
  legs_ct : ∀ z, Goods r (X.pole z)
  local_ct : ∀ z, X.pole z = Tad (X.pole z) h

namespace Good
variable {R T : Result G}

theorem usable (H : Good b r h R) : Sewable b r h (R.classicalTerm + R.pole) R.renorm :=
  H.before.plus (Sewable.ofHomogeneous H.poleShape H.after.back)

theorem after_rank (H : Good b r h R) : OfRank r R.renorm :=
  H.legs_pre.plus (collapse_rank (Eventually.of_forall H.legs_ct))
end Good

theorem sew_ok (X : Flats G) (hc : Coal b h 0 r X) (hr : OfRank r X) : Good b r h (sew h X) := by
  have hp : Sewable b r h 0 X := ⟨hc.eye,hc.force⟩
  obtain ⟨he,hw⟩ := integrate_sewable hp
  have hm := integrate_rank hp hr
  exact ⟨hc,hw,ct_kernel hw, with_pole_joint hc,hr,hm, ct_rank hw hm,
    (pole_cancels hw he hc.real).eq_tad⟩

@[simp] theorem renorm_vertex (V : LocalVertex G b h) : (instructions (vertex V)).renorm = collapsed (fun _ => V.symbol) := by
  simp [instructions, Result.renorm, collapsed]

theorem accepted (F : GraphSum G b h) : Good b F.slots h F.instructions := by
  induction F with
  | @vertex b h V =>
    let f : Coat G := fun _ => V.symbol
    have hm : Count f h := fun _ => V.scaling
    let J := instructions (vertex V)
    have ht : kPrice V.symbol := V.cap.fine.tune.mer.price.exists.choose_spec
    have HV : Stay h (collapsed f) := by
      intro y s; rw [pureP f hm]; exact Live.stays ht
    refine ⟨coal_zero b _ 0 _,Sewable.ofHomogeneous V.cap hm, Cap0.zero,?_,
      (fun _ => (washed (good V.rank G)).zero),collapse_rank (Eventually.of_forall (fun _ => V.slots)),
      fun _ _ _ _ => rfl, fun _ => (tad0 _).symm⟩
    change Joint h 0 J.renorm f 0
    unfold J; rw [renorm_vertex]
    exact ⟨vibe_root hm, HV, Moony.toast (clockMoon (Sewable.ofHomogeneous V.cap hm).clock),
      (cone G).zero_mem, mer.zero, fun _ => Home.zero _, by simpa only [add_zero] using sip_root hm⟩
  | loop U X ih =>
    have H := ih.usable
    exact sew_ok _ (coal_loop H.clock ih.after.toll U.ok) (loop_rank ih.after_rank H.clock U.ok)
  | @bridge b h U X Y ih it =>
    have H (b : Bool) : star (factor b : ℂ) = (factor b : ℂ) := Complex.conj_ofReal _
    exact sew_ok _ (glazer (coal_bridge (b:=b) ih.usable.lower it.usable ih.after.toll it.after.toll U.ok) _ (H b))
      ((bridge_rank ih.after_rank it.after_rank U.ok).realScale _)

/-- Every scale used by this forest, on the UV germ at once for each page.
Primitive vertices are at the retained cutoff also; only the *difference*
of prepared and bare-root has a scale integration. -/
theorem computed (F : GraphSum G b h) (ell : ℕ) :
    F.instructions.prep = integratePages h F.instructions.force + collapsed F.instructions.classicalTerm ∧
    ∀ᶠ z in dotty, (∀ s a (m : ℕ) (w : Legs (Shore G m)), IntervalIntegrable
      (fun t => plow (vamp z h ell) t (F.instructions.force ell z) m w) MeasureTheory.volume a s) ∧
    ∀ s, Shine.Wind (fun a => regulated a s z h ell (F.instructions.force ell z)) atBot
      (plow (vamp z h ell) s (integratePages h F.instructions.force ell z)) := by
  constructor
  · cases F <;> simp [Result.renorm,instructions,sew, integratePages,collapsed]
  simp_rw [integrate_each]
  have hx := (clockMoon F.accepted.force.eye ell).mer
  filter_upwards [hx.price,uv_limit (ell:=ell) (h:=h) hx (fun he => he ▸ F.accepted.force.force)] with z hz ht
  exact ⟨fun s a m w => interval_plow hz _ _ _ _, ht.2⟩

end GraphSum
end YM.MS.ScaleForest
