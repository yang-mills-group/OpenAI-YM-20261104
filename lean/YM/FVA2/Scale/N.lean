import YM.FVA2.Scale.Manifest
/-!
# Intrinsic position prediction & mass-independent adjustment.
Uses polynomial log test on scaled kernels and demands strict filtration drop. These
select at most one frame at each field horizon, and this definition from the Wilson
coefficients & checking their continuum predictions (coefficientwise) is meaningful. Show existence
from true implemented MS relation & powers result. Prove coincidence of implementing
map with graded diagonal variant. Next prove the precise scale law and frame group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.Measure
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Facets Equator
variable {G:Gauge}{n d e:ℕ}
section pos
variable (Y:Initialize G) {V:Normalize.Store G} (K: Rose.Pick V) (d:ℕ)
abbrev Aim (A:Way G d): Prop:= ∀ n (p:Stage n) k (v:Tags G d n), Tendsto (fun i=> Rose.measureₓ Y K d i k v) (Gate p.val) (𝓝 ( A n p k v ))
lemma unites {X Y':Way G d} (h:Aim Y K d X)(he:Aim Y K d Y'): X=Y':= by ext1 n; ext1 x; ext1 k; ext1 v; exact tendsto_nhds_unique ( h n x k v ) ( he n x k v )
-- `Gate` using the actual `Front`. Definition of this (continuum) position
-- prediction doesn’t depend on choosing any MS data.
def start : Way G d := if h:∃ A, Aim Y K d A then h.choose else 0
structure PowerCondition (X:Way G d) (N: Guard G d) : Prop where
    scale : Base N
    strict : Scale.remainder N
    homogeneous : PurePower (actMark N X)
/-- Strict triangular mass-independent adjustment. Real, unit-preserving & all-orders.
Mathematical characteristic unique: normalized functions have no different-weight
power-log contributions (criterion `homogeneous` on the separated configurations).
This criterion accompanied by an independent scale law below. Upper order restrictions
use this same convention. Not computing the finite rotation alignment for later stress tensor
and Minkowski theorem. See `Clef/Optional` for further
results allowing **within grade** changes of the below basis.
-/
def adjust : Guard G d:= if h:∃ T, PowerCondition d (start Y K d) T then h.choose else 1
def outlook : Way G d:= actMark (adjust Y K d) (start Y K d)
end pos
variable (Y:Initialize G) {V:Normalize.Store G} (K:Rose.Pick V) (ν:ℝ) {O:Booked (Press.portDeck G)} (T: MS_Data G O)
-- alignment functions.T.S exact regardless position. "$f" from χ on actual normalized tests.
abbrev liftT (d:ℕ): Guard G d:= Reg.Token.leaf_t ν K T d
abbrev chi := Reg.Choice.choice ν K T
abbrev f := Reg.Token.conversion ν K T
abbrev Z (d:ℕ) : Guard G d:= liftT K ν T d * adjust Y K d
abbrev pupil (d:ℕ): Way G d:= actMark (liftT K ν T d) (couple ( f K ν T ) (wave ν T d))
section sag
open Reg.Unique
variable (S: Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
include h hs hr hu
lemma reaches (d:ℕ) : Aim Y K d (pupil K ν T d):= fun _ x k p=> Reg.Faith.confidence ν Y K S T p h hs hr hu k _ x.property
lemma together (d:ℕ): pupil K ν T d=start Y K d:= by
    unfold start; split_ifs with H; · exact unites Y K d (reaches Y K ν T S h hs hr hu d) H.choose_spec
    exact False.elim ( H ⟨_, reaches Y K ν T S h hs hr hu d ⟩ )
lemma charges : Base ( liftT K ν T d ):= Base.equivalence _|>.mpr ( Reg.Faith.canonical ν Y K S T h hs hr hu )
omit h hs hr hu in
lemma linkage (a:d≤e): Walk a (liftT K ν T d) (liftT K ν T e):= Walk.steps (show Walk a (Reg.State.chooseL ν V T d) (Reg.State.chooseL ν V T e) from fun _ p => Reg.State.chainL ν V T a p ) _
include ν
lemma inherited (a:d≤e): Inherited (start Y K d) (start Y K e) a:= by simp_rw [ ← together Y K ν T S h hs hr hu ]; exact unfold_acts _ _ a _ _ ( unfold_team _ _ a _ (wave_walk ν T a) ) (linkage K ν T a)
lemma dawn : StarGround ( start Y K d ):= ( together Y K ν T S h hs hr hu _ ) ▸ step_mark _ _ ( charges Y K ν T S h hs hr hu ) ( step_dawn _ _ (before ν T) )
local notation "L"=> liftT K ν T
local notation "H"=> start Y K
local notation "P"=> PowerCondition
lemma matter : P d ( H d ) ( mirror ( L d ) * Scale.diagonal (L d) ):= by
    let A:= L d; obtain hc : Base A:= charges Y K ν T S h hs hr hu; let U:= H d; refine ⟨hc.rewind.mul hc.payment, ?_, ?_⟩;
    · unfold Scale.remainder; rw [ hc.rewind.guard hc.payment,hc.diagonal_rev, Base.house.mp ( Base.native (L d) ),hc.payment.turn ]
    rw [ ← together Y K ν T S h hs hr hu ]; unfold pupil; rw [acts,← mul_assoc,hc.turn',one_mul]; exact powers_m _ _ ( powers_t _ _ (Equator.smooth ν T Y S h hs) ) ( Base.native _ ) -- A defeq issue
lemma matchU (N:Guard G d)(he: P d (H d) N) : N = mirror (L d) * Scale.diagonal (L d):= by
    have hv := charges Y K ν T S (d:=d) h hs hr hu; let B:= couple ( f K ν T ) ( wave ν T d ); have ht: actMark ( (L d)*N ) B=actMark N (H d):= by rw [← acts B,← together Y K ν T S h hs hr hu ]
    have Ht := Manifest.bill B ( (L d)*N ) T Y S h hs (hv.mul he.scale) ( powers_t _ _ (Equator.smooth ν T Y S h hs) ) ( step_dawn _ _ (before ν T) ) ( ht.symm ▸ he.homogeneous ); have hn := Base.house.mp Ht; rw [ Base.guard hv he.scale, he.strict, mul_one ] at hn; rw [ hn,← mul_assoc, hv.turn,one_mul]; -- orientation
lemma adj : PowerCondition d (start Y K d) (adjust Y K d):= by
    unfold adjust; rw [dif_pos ( show ∃ T',PowerCondition d (start Y K d) T' from ⟨ _,matter Y K ν T S h hs hr hu⟩ ) ]; apply Classical.choose_spec
lemma onlyT (T':Guard G d): PowerCondition d (H d) T' ↔ T'= adjust Y K d:= by
    constructor; · intro hp; rw [ matchU Y K ν T S h hs hr hu _ hp, matchU Y K ν T S h hs hr hu _ ( adj Y K ν T S h hs hr hu ) ] -- adjust appears. maybe
    rintro rfl; exact adj Y K ν T S h hs hr hu
lemma grades (a:d≤e): Walk a (adjust Y K d) (adjust Y K e):= by
    let X:=L d; rw [ ← (onlyT Y K ν T S h hs hr hu _).mp ( matter Y K ν T S h hs hr hu ), ← (onlyT Y K ν T S h hs hr hu _ ).mp ( matter Y K ν T S h hs hr hu ) ]; have hk:= linkage K ν T a; exact (hk.rewind (charges Y K ν T S h hs hr hu) (charges Y K ν T S h hs hr hu)|>.mul hk.grades)
lemma paths (a:d≤e): Inherited (outlook Y K d) (outlook Y K e) a:= unfold_acts _ _ a _ _ ( inherited Y K ν T S h hs hr hu a ) ( grades Y K ν T S h hs hr hu a )
local notation "Φ"=> Z Y K ν T
lemma equator : Φ d=Scale.diagonal (L d):= by rw [ Z, ← (onlyT Y K ν T S h hs hr hu _).mp (matter Y K ν T S h hs hr hu), ← mul_assoc,( charges Y K ν T S (d:=d) h hs hr hu ).turn', one_mul]
lemma precise : Native ( Φ d ):= by rw [equator Y K ν T S h hs hr hu]; exact Base.native _
lemma litZ : Base (Φ d):= Base.mul ( charges Y K ν T S h hs hr hu ) ( adj Y K ν T S h hs hr hu|>.scale )
lemma walks_o (a:d≤e) : Walk a (Φ d) (Φ e):= ( linkage K ν T a ).mul ( grades Y K ν T S h hs hr hu a )
lemma scaled_sigma : StarGround (outlook Y K d):= step_mark _ _ ( adj Y K ν T S h hs hr hu|>.scale ) ( dawn Y K ν T S h hs hr hu )
theorem compares : actMark (Φ d) ( couple ( f K ν T ) ( wave ν T d ) )= outlook Y K d:= by unfold Z outlook; rw [ ← acts ]; exact congr_arg _ (together Y K ν T S h hs hr hu d)
end sag
end YM.FVA2.Scale.Measure
