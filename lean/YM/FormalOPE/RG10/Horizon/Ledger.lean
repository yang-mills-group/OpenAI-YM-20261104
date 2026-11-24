import YM.FormalOPE.RG10.Horizon.BasisCash

/-!
# Putting the period-comparison supplies on formal k-far

This is the exact *type* of data sufficient for the analytic core here. Use only with the
appropriate construction of the cylinder/location/Fk scheduler from the declared block & noise,
data from THAT Wilson germ and gauge convention. Will use its coherence with the completely
independent TREE-orbit WilsonX on the same field basis and orientation and on the given real
arrays by asserting the per-period estimates (on **correlations**, in Window file). No claiming
these data or estimates yet instantiated by the trajectory builder. In particular `Ledger.K` must
support estimation with the actual period and gauge-adapted representatives for multi-mark unions.

Opaque slots/readers are separate; all budget fields in `FilmBook` etc here and in `Capture`
precisely control geometry and estimates needed *without* assuming a k-far difference bound. Cost
of single-anchor soft transports and hypothesis on sizes of the exterior single stream remain
ports. If using an exterior field product, its through-history budget of `W.value` as a stream must
be proved too: one version uses the mutually separated labels and posteriors via Weave.propagates.

This version works with finitely many orientations at a frame. So need episodic proof that the
per-terminal-cell/origin averaging and any displacement seam requirements are accomplished (or
approximated to sought precision) by these same shifts; applying an arbitrary single twisted-origin
evaluation with no such per-observable comparison to the same-regulator data isn't licensed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{m r d:ℕ}

/-- Raw common episode/contour data for a chosen estimate on Fore cluster of positions at
resolution μₖ = μDesired (relative to the length-unit diag frame at 1; default 1). Size, coupling openness, restricted pole, and geometry matches given per use.
The root untested process and projection are common (chosen without far probe response).
Gauge/frame/regulator origin arrangement belongs on this data. `puffs` convert the **dimensionless
b** units of restored word around projected root, not number of locations, TO the h physical basis
in diagrams at **length one**. Need its genuine frame relation (if `k` is there, when deriving from `report`, act by
`((μ_b/μ_k)^m)` and inverse coordinate roll too into Deck h); compare below on necessary scalar
observables. Only this exact algebraic/cost interface consumed (not asserting origin parity or
constructor/order coherence follows automatically). $μ_N=a_N$ in report units. Use 
coupling $g_X'$ at **unit length**, the same at the epoch: generators reexpressed including the Fk k-leg-and-roll change and
real conversion with its finite regulator detector parameter. -/
structure Ledger (F:Frames G)(h:ℕ)(μDesired : ℝ := 1) where
  block : ℕ+
  topIndex : ℕ -- number of q regularizer steps; linear data & regulators frozen accordingly
  N : ℕ
  measure : ℕ
  capture : ℕ
  oldest : ℕ
  sequences : oldest ≤ capture ∧ capture ≤ measure ∧ measure ≤ N
  X : Type
  T : ℕ→Type -- root stamps side at mesh
  U : ℕ→Type -- field locations
  J : ℕ→Type -- Wick sqrt ports
  K : ℕ→Type -- kernel lifts
  [x : MeasurableSpace X]
  [add : ∀ i,AddCommGroup (K i)]
  [moduleRow : ∀ i,Module Series (K i)]
  [rootFin : ∀ i,Fintype (T i)]
  [links : ∀ i,Fintype (U i)]
  [sqrtFrame : ∀ i,Fintype (J i)]
  [distU : ∀ i,DecidableEq (U i)]
  Test : Type
  Stamp : Type
  Slot : Type
  [se : Fintype Slot]
  view : Voyage U J
  tape : Scale X U
  k_length : tape.μ measure=μDesired
  top_length : tape.μ N = LatticePT.epsilon block topIndex
  fibers : Fibers T
  patch : Locale T X Test Stamp
  cylinder : Cylinder T U K Test Slot
  frame : ∀ i, Subalgebra ℂ (Channel (U i))
  radius : Capture.Cover tape patch capture
  admit : Submodule Series (K capture)
  filmF : K capture
  Players : Type -- catalog of inner coordinates, pretest root families W-angle postshift. term rank/time cost envelope explicit below
  Word : Finset Players
  topChannel : Players→ Channel (U N)
  g : Players→ X→ℂ
  puffs : Slot→Deck F h → Series

attribute [instance] Ledger.x Ledger.add Ledger.moduleRow Ledger.rootFin Ledger.links Ledger.sqrtFrame Ledger.distU Ledger.se
namespace Ledger
variable {h n : ℕ} {μDesired:ℝ} (L : Ledger F h μDesired)
local notation "λ₀" => L.tape.μ
local notation "Γ" => L.Slot → Series
local notation "μ" => L.measure
abbrev design := Cylinder.designated L.cylinder L.filmF L.oldest
abbrev chimney (u:L.Test)(s:L.Slot→Series) := Cylinder.coupon L.tape h L.cylinder u L.capture L.N s
def basis (j:L.Slot) : L.Slot→Series:= Pi.single j 1
def article (j: Deck F h) := realCase (∑ i, design L i * L.puffs i j)
/-- One oriented footprint in the bulk estimate. -/
structure Door (r:ℕ)(L:Ledger F h μDesired) where
  tone : ℕ -- near representative of far length
  u : ℕ -- terminal echo
  mark : Type
  test : L.Test
  C : ℝ -- Y cost cap
  share : ℝ -- attenuation exponent
  δ : ℕ
  lines : Finset mark
  D : mark → ℕ
  j : mark → ℕ
  H : mark → ℕ
  label : L.X → mark → Channel (L.U L.N)
  arch : L.X → mark → Lens L.tape.tape
  archive : L.X → Lens L.tape.tape
  rank : ℕ
  rank1 : ℕ
  n : ℕ
  future : ℕ
  nearFar : Lens L.tape.tape
  terminal : Lens L.tape.tape
  distant : Lens L.tape.tape
  certified : Install L.tape L.patch L.fibers L.view L.cylinder L.frame L.capture L.measure tone L.oldest L.N r rank rank1 n future δ h L.radius L.filmF L.admit test C share archive L.Word L.topChannel L.g lines D H j label arch nearFar terminal
  exterior : Channel (L.U L.N)
  d₂ : ℕ
  p : ℕ -- exterior quote
  q : ℕ
  ν : ℕ -- soft segment exponent
  hardly : ∀ i∈Icc tone L.N,L.tape.value i (maximumNeeded n r rank) r distant (L.view.yield i L.N exterior) ≤ tally L.tape C (L.tape.μ tone) i p q
  team : rank1+d₂ ≤ rank
  guard : Guard exterior r d₂
  pose : exterior∈L.frame L.N
  near : terminal.m ≤ nearFar.m
  far : terminal.m ≤ distant.m
  dist : nearFar.Spaced distant (L.tape.μ tone / C^δ)
  book : max (∑ i∈lines,H i) h + q+2+h ≤ n
  stop : u ≤ L.oldest
  supports : Fence L.view L.tape terminal (fun i=> (L.frame i).toSubring) r n rank u tone ((L.tape.Y C (L.tape.μ tone) L.capture)^ν)
namespace Door
variable {L} (W : Door r L)

def given := echo L.view W.u L.N ((smear L.tape L.patch L.capture L.N L.radius L.topChannel L.g L.Word W.test)* W.exterior)
def poseAt (W: Door r L) (j : L.Slot→Series) := echo L.view W.u L.N ((L.chimney W.test j)* W.exterior)

local notation "V" => W.u
local notation "T" => W.tone
local notation "A₀" => L.tape.Y W.C (L.tape.μ W.tone) L.capture
local notation "δ" => W.δ

def income := A₀ ^ Install.quiver (Film.toBook r W.rank W.future W.δ (∑ i∈W.lines,W.j i) (∑ i∈W.lines,W.H i)) W.δ
lemma shutter : scaleC r L.design ≤ W.income:= Install.home W.certified

def payment :=
 let J := ∑ i∈W.lines,W.j i
 let H := ∑ i∈W.lines,W.H i
 let K:= max W.p (Install.arity r W.rank W.future δ J H)
 A₀ ^ W.ν * (A₀ ^ (Far.invoice r W.rank W.n δ K W.q (max H h) h)*L.tape.fade (h+W.share) L.capture W.tone)
lemma toll : rate r (W.given - W.poseAt L.design) ≤ W.payment:= by
 unfold given poseAt; rw [show chimney L W.test L.design = _ from (shiny L.filmF W.test L.sequences.1 L.sequences.2.1 L.sequences.2.2).symm];
 exact W.certified.voices W.hardly W.team W.guard W.pose W.near W.far W.dist W.book (W.stop.trans W.certified.order.2.1) W.supports
-- price skipped columns before any uv or IR estimate
lemma every_slot : W.poseAt L.design= ∑ i,L.design i* W.poseAt (L.basis i):= by
 let f : (L.Slot→Series) →ₗ[Series] Series :={
  toFun := W.poseAt
  map_add' x y:= by simp only [poseAt, chimney,Cylinder.coupon,map_add, add_mul]
  map_smul' c x:= by
    unfold poseAt chimney Cylinder.coupon; simp only [map_smul,RingHom.id_apply]; rw [smul_mul_assoc, echo_linear L.view (W.stop.trans (le_trans L.sequences.1 (L.sequences.2.1.trans L.sequences.2.2)))]; rfl }
 let x:=L.design; have he:x=∑ i,x i • (basis L i):=by ext1 i; rw [Finset.sum_apply]; simp [basis,Pi.single_apply,mul_ite]
 change f _=_; nth_rw 1 [show L.design=_ from he]; rw [map_sum]; simp_rw [map_smul]; rfl
end Door
end Ledger
end YM.FormalOPE.RG10.Clearing
