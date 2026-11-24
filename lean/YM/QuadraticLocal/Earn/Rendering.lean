import YM.QuadraticLocal.Earn.Passport
import YM.QuadraticLocal.Lamps
import YM.QuadraticLocal.Sunrise.Loan
import YM.Next.SCHEDULE.TensorCost
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Placement
import YM.Extra.ITERATION_NO_LOSS.TermNorm
/-! # Render each analytic marker row at this stencil convention

Orders `Loan.e≥0` in the fluctuation/potential Taylor convention. Render the atom with
its lag power of the coupling, which may be negative. Thus this is NOT a substitution of a
complex field germ; evaluates real fields and masks on all terms.

On the incoming Phi use the actual `Coat.gStep R.beta`. On the outgoing Phi may receive
un-reset values; the perturbative projection has to agree with this convention too. On resetting
power later regenerate the `Row`s, not just their `income`. `funds` of a Row is chosen BEFORE
any painting by the tests. Color needn't be real. This interface takes the whole test parameter
set; the witness of multilinearity, continuity etc on them isn't required in the `Offers`
price, so that when we transmit terms as error with the full-gauge proof we can paint them with
test functions given as exact kernel-address reads or as more general amplitude variation.

Path length receipt is on genuinely exposed length, including lifted/wrapping by this `Atom` and
this full binder. A presentation as a countable (not necessarily finite) collection of these
is the basis of the exponential kernel budget for analytic inputs and the next-step output.

WEIGHT on `Offers` uses μ also on the field path piece of length, *before* normalizing the
atom required on the query. Thus to get `Offers b C` from the typical analytic stencil norm
buy enough to pay TWICE the field-path rate and this also with all `paint` cost and gauge
certificate. This currency itself doesn't assume advanced analytic inputs or Fk propagation.
Sizes of all support masks quoted here are upper bounds, not inferred from occurrence count.

We systematically use literal complete Hart.P (regular support), and budgeting at EVERY root
in it. Derivative norm includes the regular law on this support, with boundary-equality convention
on flags. Support declares stencil not just positivity region for the rendered f.
 Computation of the mask itself may of course query flags on this support (definition `Healthy`);
 the numerical push charges the actual inspected support accordingly. No transporting derivative
 to a strictly larger Region from an estimate at a different step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice RG Wilson Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6
open AnalyticBridge VerifiedReset Collection Precision Exterior Extra.Iteration Next.Scheduling Next.Foundations
open QuadraticLocal.Sunrise
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type*}[DecidableEq V]{G:Gauge}{n:Side}
variable (P:Passport n V)(R:Census V)
structure Row (P:Passport n V) (R:Census V) (G:Gauge) (α:Type*) where
    binder : Binder P R
    lamp : Loan
    atom : Atom G lamp.r
    lawful : atom.Invariant
    clear : Prop
    salary : ℝ
    sound : 0 < salary
    paint : α → ℂ
    rank : clear → lamp.r=0

variable {R P}
namespace Row
variable (T:Row P R G α)
abbrev mode : R.Mode:= T.binder.mode
def center := T.binder.center
def Credentials (u:ℕ) (p:V→ℕ): Prop:= T.lamp.e ≤ u ∧ T.lamp.toll= ∑ i∈T.mode.val,p i
def Graceful (σ:ℝ):Prop:= T.atom.budget σ ≤ 1
protected def Budget :Prop:= ∀ t:α, ‖T.paint t‖ ≤ T.salary
def length : ℕ:= T.binder.length+T.atom.length
def height (b:ℝ) := T.salary * Real.exp (b*T.length)
variable (B:BudgetPoint)(g:ℝ)
-- need norm-geometric cutoff ON REAL (threshold here not derivative estimate type of α).
abbrev Short (b:ℕ) : Prop:= T.length ≤ b
-- don't specialize clear. May price support there too.
def region (b:ℕ) : Support n:= if T.length≤b then neighbors (b+1) T.center else T.binder.ground T.atom
abbrev ground := T.region B.B
lemma cleared (b:ℕ)(h:T.Short b): T.region b=neighbors (b+1) T.center:= if_pos h
lemma within (b:ℕ): T.binder.ground T.atom ⊆ T.region b:=by
    unfold region; split; next h=> exact fun i hi=> (neighbors_mem ..).2 ((T.binder.spread (J:=T.atom) hi).trans (h.trans (Nat.le_succ b))) -- J explicit not named? `_`
    next=>rfl
lemma starts (b:ℕ): T.center ∈ T.region b:= T.within b (T.binder.first T.atom)
lemma footprint : T.atom.footprint T.center ⊆ T.ground B:= Subset.trans (T.binder.footprint T.atom) (T.within _)
lemma heard (b:ℕ)(i:V)(hi:i∈T.mode.val): P.support i ⊆ T.region b:= Subset.trans (T.binder.covers T.atom i hi) (T.within _)

def radius (b:ℕ):= b+1+T.length
lemma near (b:ℕ)(x:Site n)(h:x∈ T.region b):separation T.center x≤ T.radius b:= by
    unfold radius; unfold region at h; split at h
    next=> exact ((neighbors_mem ..).1 h).trans (Nat.le_add_right ..)
    next=> exact (T.binder.spread T.atom h).trans (Nat.le_add_left ..)
lemma tiles (b:ℕ)(hp:0<b): b * coverNumber b (T.region b) ≤ (1000+T.lamp.r+T.mode.val.card)*b+T.length:= by
    unfold region; split
    next h=>
       have hx:coverNumber b (neighbors (b+1) T.center) ≤ (2+2+1)^4:= (Corona.cover_mono (Corona.halo_mono (show b+1≤2*b from by omega) (Finset.Subset.refl _)) _).trans (Corona.tile T.center 2 b hp)
       have he:=Nat.mul_le_mul_left b hx; norm_num at *; nlinarith only [he,h]
    next=>
       apply (T.binder.charge T.atom hp).trans
       change _ ≤ _+ (T.binder.length+T.atom.length); calc
           _ = (1+T.lamp.r+T.mode.val.card)*b+T.binder.length+T.atom.length:= by abel
           _ ≤ _:= by nlinarith

-- all masks have actual numeric values on every configuration even behind flags. Qualitative & derivative purchases are on Healthy complete, not on everywhere.
def grain (g:ℝ) : Config G n → ℝ:= fun U=> g^T.lamp.lag * T.atom.unmasked U T.center

def nominal (g:ℝ)(t:α): Config G n → ℂ:= T.paint t • (fun U=> (T.grain g U:ℂ))
lemma regular : B.Regular (T.ground B) (T.grain g):= CouplingShape.reg_scale _ (CouplingShape.reg_extend (Derivs.canonical_regular _ _ _ T.lawful) (T.footprint B))
lemma real_quote : B.supBounds T.center (T.ground B) (T.grain g) (|g^T.lamp.lag| * Wages.price B T.atom):= CouplingShape.sup_scale _ (sup_larger (Wages.total B ..) (T.footprint B))
lemma legal (t:α) : B.Regular (T.ground B) (T.nominal g t):= regular_smul _ (regular_mapped Complex.ofRealCLM (T.regular B g))
def baseCost (g:ℝ) := ((1+(T.radius B.B:ℝ))^B.power)^B.order * (|g^T.lamp.lag| * Wages.price B T.atom)
def charge (g:ℝ):= T.baseCost B g * T.salary
lemma supported (t:α)(o:Site n)(ht:T.Budget)(hx:o∈ T.ground B): B.supBounds o (T.ground B) (T.nominal g t) (T.charge B g):=by
    have hr:B.Regular (T.ground B) (fun (U:Config G n)=> (T.grain g U:ℂ)):= regular_mapped Complex.ofRealCLM (T.regular B g)
    have hp:= (sup_real (T.regular B g)).2 (T.real_quote B g)
    have hx:B.supBounds o (T.ground B) (fun (U:Config G n)=> (T.grain g U:ℂ)) (T.baseCost B g):= by
       apply Push.Local.bound_weaken (Push.Local.bound_shift hp hr o); apply mul_le_mul_of_nonneg_right _ hp.1; gcongr; exact near T _ _ hx
    exact Push.Local.bound_weaken (bound_smul _ hx) ((mul_le_mul_of_nonneg_right (ht t) hx.1).trans_eq (mul_comm ..))
lemma quietU (o: Config G n)(h:T.clear): T.atom.unmasked o T.center=T.atom.unmasked 1 T.center:= by
   have he:= T.rank h; unfold Atom.unmasked; apply congr_arg T.atom.poly; funext i; exfalso; have ht:= i.prop; omega
lemma constantT (t:α)(o:Config G n)(h:T.clear): T.nominal g t o=T.nominal g t 1:= by unfold nominal grain; simp only [Pi.smul_apply]; rw [T.quietU o h]
end Row

section budget
variable (X : ι → Row P R G α)(w:V→ℝ)
set_option quotPrecheck false
local notation "κ"=> Poly.toll w
-- per-center in the specified physical support. Allows a stochastic upper probe stronger than point e.g. buying any apertures to bound ∑tails of analytic outputs. Rough.Hit etc separate. This is still anchored.Ph.Mark not volume.

def Offers (a c : ℝ) : Prop:=∀ x:Site n, SumBudget (fun i=>if (X i).center=x then κ (X i).mode * (X i).height a else 0) c
-- Crew obligations at ALL spheres.E.Pos power
structure Issues (a:ℝ)(k:ℕ)(u:V→ℕ):Prop where
    spend i: (X i).Graceful a
    usable i:(X i).Credentials k u

variable (B:BudgetPoint)

def rendered (g:ℝ) : Lamps α ι G B P.origin R where
    mode i:= (X i).mode
    live i:= (X i).binder.live
    address i:= ⟨(X i).center,(X i).ground B,(X i).starts _⟩
    roots i v hv:= (X i).heard _ v hv (P.born v)
    nominal t i:= (X i).nominal g t
    legal t i:= (X i).legal B g t
    clear i:= (X i).clear
    pure t i U:= (X i).constantT g t U
end budget
end YM.QuadraticLocal.Earn
