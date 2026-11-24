import YM.FormalOPE.RG10.Horizon.Ledger
/-!
# Compare at a match of clocks & field convention (explicit quantitative regulator hypotheses)

Domain physically meaningful: $\log(T)=s$ scales on `Arrangements.Fore m` for genuine chosen `x`
and only the probes being read at THIS epoch. `Stretched` hypothesis (separate RG09/08/06/11
contributions) is a cyclic coherence contract that still needs assembly and all listed estimates,
**not here solved**. Includes comparing all moments at this moving cutoff/IR procedure to the
same labeled and normalized WilsonX orbit computation, not from just the fixed-volume identities.

Rotations choice paid as normalized mass. The clocks use common g_X' at the epoch-reference length one k (not necessarily `measure` when μDesired changes);
angular shift chosen after reading extent (same prefix measurement/capture/input set/lifts/and
stop projector b→s for that comparison). Requires from generator: correctly and independently
construct/provision all gate/axis eligibility including placement and measurement-length/coupling &
frame adapters; see `Ledger`, PROGRESS. Numerical conditions `ink` and `gap` contain
only clock/distance/moment exponents (not a bound on joined-budgets); supplied examples
with common block and poly log Y, capture size controlled & enough terminal decay from the
stepped-lattice poles may use those arith bounds. Don't use adaptive periods giving hidden growth
in those estimates.

Charge heights in the program through `m,r`; moments also from the demand in
`Door.membership` etc. No results here assert these hold at any finite step count on the actual
construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{m r h d:ℕ}

-- regulator counterpart, one-sided code for real measured fps. Keep explicit q controller here.
variable {μDesired : ℝ} (L:Ledger F h μDesired) (X₁: Vantage F)
namespace Ledger
variable (P R)

def reapply {k:ℕ} (x:Fin m→ Seats F d)(B: YM.Test (m+k))(v : Fin k→ Seats F r) : fps :=
    Panel.valuation (fun w => Grade.Rails.coarse R (P:=P) L.block L.topIndex (max d r) ⟨⟨m+k,B⟩, w⟩)
      (Fin.append (Panel.promote (le_max_left ..) ∘ x) (Panel.promote (le_max_right ..) ∘ v))
local notation "K" t => trail R (-(t)) ∘ X₁.fields

def runHere (E: Fore m) (x: Fin m→ Seats F d) (t:ℝ) := if h:E.budget < Real.exp t * X₁.rear.gap then L.reapply R P x (Arrangements.test E _ t h) (K t) else 0

def runOne (t:ℝ) (j:Deck F h) := L.reapply R P (fun _:Fin 1=>seat j) (silver X₁.rear t) (K t)

variable {P R L} (Z R) (E: Fore m) (x:Fin m→ Seats F d) (s:ℝ)

-- here mathematical worker must choose appropriate age/scale comparison conventions,
-- one geometry orientation-frame token family.
structure Orbits (L:Ledger F h μDesired) (r:ℕ) where
  count : ℕ
  nonempty : 0 < count
  rotates : Fin count → Door r L
  weight : Fin count → ℝ
  positive i : 0 ≤ weight i
  counting : ∑ i,weight i=1
namespace Orbits
variable {Z R}
variable (O:Orbits L r)
def avg (x:Fin O.count→ Series):= ∑ i, PowerSeries.C (O.weight i:ℂ) * x i

def mixedAt := O.avg fun i=> (O.rotates i).given
def plain (p:L.Slot→Series) := O.avg (fun i=> (O.rotates i).poseAt p)
def compose (q:L.Slot→ Series) (T:Deck F h→fps) := ∑ i,q i * ∑ j,L.puffs i j * into (T j) -- no O
lemma mid : O.plain L.design=∑ i,L.design i* O.plain (L.basis i):= by
 unfold plain avg; simp_rw [(O.rotates _).every_slot, Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro _ _; ring

lemma ave_sub (x y: Fin O.count→Series): O.avg (x-y)=O.avg x-O.avg y:= by
 unfold avg; simp_rw [Pi.sub_apply,mul_sub,sum_sub_distrib]
lemma bound {t} (u: ∀ i,(O.rotates i).payment ≤ t): rate r (O.mixedAt-O.plain L.design) ≤ t := by
 unfold mixedAt plain; rw [← O.ave_sub]; apply (rate_fore ..).trans;
 apply le_trans (b:=∑ i, O.weight i*t) (sum_le_sum ?_ ) _
 · intro i _; apply (rate_mul ..).trans; rw [rate_number _ (O.positive i)]; exact mul_le_mul_of_nonneg_left ((O.rotates i|>.toll).trans (u i)) (O.positive i)
 rw [← Finset.sum_mul,O.counting,one_mul]
omit O
end Orbits
-- structural size, not from any actual phase computation

def legUp (t:ℝ) (M:ℝ) (q:ℕ) := M*(1+|t|)^q
def tilt (t α:ℝ) := Real.exp (-t*α)

lemma leg_nn (t:ℝ)(M:ℝ)(q:ℕ)(h:0 ≤ M):0 ≤ legUp t M q:=by unfold legUp; positivity
lemma big_leg (t:ℝ)(M:ℝ)(q:ℕ)(h:1 ≤ M):1 ≤ legUp t M q:=one_le_mul_of_one_le_of_one_le h (one_le_pow₀ (Position.Grade.Polys.rise t))
variable (L)
local notation "F₁" => burst R Z X₁ s E x
local notation "F₀" => runHere R P L X₁ E x s
local notation "ι" => Deck F h

-- Include topology/geometry in the actual supply statement taking the cofinal trajectory.
structure Opened (P:Plan F) (L:Ledger F h μDesired) (D:ℕ) : Prop where
 block : 1 < L.block.val
 odd : _root_.Odd L.block.val
 ready : IsUnit (coeff 1 (Plan.coin F P L.block L.topIndex))
 exams d (hz:d ≤ D) : (P.beginsAt L.block L.topIndex d).Regular (fun v => constantCoeff (P.begins L.block L.topIndex d v))

-- on orbit `Stamp` side with genuine Coupon at b and reduced projection at k. Hypotheses on
-- ink and shift bias apply to **all tested pair/field columns through this horizon**, not
-- solely the estimate for output of a match on a chosen cluster. Include norm-preserving quantities
-- of the frame projection. Does NOT require assuming the wanted smallness of replacing the cluster.
structure Paid (R:Rails F) (Z:Patience P Y) (x:Fin m→ Seats F d) (E:Fore m) (X:Vantage F) (s:ℝ) (O:Orbits L r) (ink ν:ℝ) : Prop where
  opens : Opened P L (max 6 (max d (max h X.horizon)))
  capacity : E.budget < Real.exp s * X.rear.gap
  anchor i : (O.rotates i).income ≤ ink
  gains i : (O.rotates i).payment ≤ ν
  meshes i : let t:=L.tape.μ (O.rotates i).tone; Real.exp s/ink ≤ t ∧ t ≤ Real.exp s*ink
  -- these two ARE overlap estimates, RG09 must supply with all needed budgets including shifted
  -- orbit origin/cell translation and operator projection (small errors concentrated per composed orientation)
  gauge_mark : rate r (into (runHere R P L X E x s)- O.mixedAt) ≤ ν
  gauge_basis i : rate r (O.plain (L.basis i)- ∑ j,L.puffs i j * into (runOne R P L X s j)) ≤ ν
  conversion i : scaleC r (L.puffs i) ≤ ink
  -- cut and termination errors for the ORBIT and all position operations to limit
  border : coin r ((burst R Z X s E x)-runHere R P L X E x s) ≤ ν
  border_b j : coin r (runOne R P L X s j - imply R Z X s h (seat j)) ≤ ν

namespace Paid
variable {L Z R X₁ x E s} {O:Orbits L r}{M N : ℝ} (h0:0 ≤ M)(h1:0≤ N) (D : Paid L R Z x E X₁ s O M N) -- arg order?

include D
lemma leading_budget : scaleC r L.design ≤ M:= let i : Fin O.count := ⟨0,O.nonempty⟩; ((O.rotates i).shutter).trans (D.anchor i)

include h1
lemma conversion_b (i : L.Slot) : rate r (O.plain (L.basis i)- ∑ j, L.puffs i j* into (imply R Z X₁ s h (seat j))) ≤ N + M*N := by
 let b := fun j=> imply R Z X₁ s h (seat j); let B:= runOne R P L X₁ s; let G(j):= L.puffs i j;
 have he : rate r (∑ j, G j* (into (B j)-into (b j))) ≤ M*N :=
   (rate_many _ _ _ (fun k=>by rw [← _root_.map_sub]; exact D.border_b k)).trans (mul_le_mul_of_nonneg_right (D.conversion i) h1)
 let c:= O.plain (L.basis i); simp_rw [mul_sub,sum_sub_distrib] at he
 exact le_trans (le_of_eq (by rw [show c-∑ j,G j* into (b j)=(c-∑ j,G j * into (B j))+((∑ j,G j*into (B j)) - ∑ j,G j * into (b j)) from by abel])) (le_trans (rate_add ..) (add_le_add (D.gauge_basis i) he)) -- opacity maybe

include h0
lemma resp : rate r (O.plain L.design-∑ i,L.design i * (∑ j, L.puffs i j* into (imply R Z X₁ s h (seat j)))) ≤ M*(N+M*N):= by
 rw [O.mid, ← sum_sub_distrib]; simp_rw [← mul_sub]; exact (rate_many _ _ _ (D.conversion_b h1)).trans (mul_le_mul_of_nonneg_right D.leading_budget (by positivity))

lemma interpreting : coin r (burst R Z X₁ s E x - imply R Z X₁ s h L.article) ≤ N+(N+N+M*(N+M*N)) := by
 let L' := imply R Z X₁ s h
 let c:= ∑ i,L.design i * ∑ j,L.puffs i j * into (L' (seat j))
 let b:= runHere R P L X₁ E x s; let x₀:= O.plain L.design; let a:= burst R Z X₁ s E x;
 have he : realCase c=L' L.article:= by unfold c; rw [Clearing.from_full]; exact Clearing.sums_real (L:=L') (fun j=>∑ i,L.design i*L.puffs i j)
 have hp : coin r (b-L' L.article) ≤ rate r ((into b)- c):= by rw [← he]; apply (le_of_eq (Eq.symm ?_)).trans (real_paid _); rw [_root_.map_sub,real_from];
 apply (le_trans (b:=coin r (a-b)+coin r (b-L' L.article)) ?_ (add_le_add D.border (le_trans hp ?_)))
 · convert! coin_add (a-b) (b-L' L.article) using 1; congr 1; abel
 conv_lhs=> rw [show into b - c= (into b - O.mixedAt)+(O.mixedAt-x₀)+(x₀-c) from by abel]
 apply (rate_add ..).trans; apply add_le_add ((rate_add ..).trans (add_le_add D.gauge_mark (O.bound D.gains))) (D.resp h0 h1)
end Paid
end Ledger
end YM.FormalOPE.RG10.Clearing
