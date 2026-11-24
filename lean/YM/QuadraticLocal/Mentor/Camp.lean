import YM.QuadraticLocal.Mentor.Rated
import YM.QuadraticLocal.Mentor.Tuition
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Mentor
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration
open ThroughLaunch Height Opera Boulevard Trio Slide Sienna Fare Lapis Coat
open Input Org Supply Roost Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Burn AllOrder.Ink AllOrder.Ink.Money
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Wheel
open AllOrder.Wheel.Ride AllOrder.Wheel.Ride.Pair AllOrder.Catch
open QuadraticLocal.Sunrise QuadraticLocal.Echo RemainderComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {V:Type}[Fintype V][DecidableEq V] {G:Gauge} {X: Metals G}
variable (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (D:Rolls X.p) (Q:R.Tab D)
/-!
# Publication calendar: buy all eligible requests before running

Keyed by `Opportunity` (two halo budgets `u=count` & `s=height`, current stage pair),
`Epoch` (actual vacuum order), and `Ticket` (specimen of a combination with ≤ `u` distinct
marked elementary inputs). These are FINITE sets at each stage pair even when post-L currency
changes with t. This bookkeeping allows ANY AUTHORIZED RUN in the strengthening, all volumes
and all requested orientations. Consumers take parameters and costs literally.

Earn `MarkHours` whenever illumination is requested; keep even analytic potential field rank
and canonical completions all the way through estimates. The interpretation in terms of
ProtoEpoch/Beta comes separately. Holder sizes.W.C.Seam.State are in TWO exponent-moment
classes (book width for inputs and width for outputs). For recurrence recognition need their
comparison through all (x,y) transitions.R.Descriptor.Clock.Weight.*.
-/
open AnalyticBridge.VerifiedReset
variable {Z:Targets X.p X.K} {E:Expenses Z}{p:Return.Wages}{z:ℕ→ℝ} (W: Repeat.Register D E p z) {M:ℕ→ℕ→Postage} (S: AnalyticBridge.VerifiedReset.Time.Scouts (F:=M))
set_option quotPrecheck false
local notation "Φ" x:max y:max=> (W.μ x y)
local notation "L" x:max=> (D.L x)
variable (ψ:ℕ→ℕ)(x y:ℕ)(h:StepStages x y)
/- Pre-L widths tuned.Can be extended by other geometry ledgers. -/
structure Opportunity (x y:ℕ) where
    count : ℕ
    stage : ℕ -- purchased Height power.U arg. Energy stamps all of this size
    meet : StepStages x y
    countFits : count ≤ y
    stageFits : stage ≤ y
    pos : 1≤ stage
local notation "Ht"=> Opportunity x y
namespace Opportunity
instance : Finite (Opportunity x y) := by
 let f(i:Opportunity x y): Fin (y+1) × Fin (y+1):=(⟨i.count,Nat.lt_succ_of_le i.countFits⟩,⟨i.stage,Nat.lt_succ_of_le i.stageFits⟩)
 refine Finite.of_injective f ?_; rintro ⟨u,s,h1,h2,h3,h4⟩ ⟨u',s',h5,h6,h7,h8⟩ hv; have ha:u=u':= congr_arg (Fin.val ∘ Prod.fst) hv; have hb:s=s':=congr_arg (Fin.val ∘ Prod.snd) hv; subst u' s'; rfl
end Opportunity
structure Epoch (r: Opportunity x y) where
    vac : ℕ
    wants : 4≤ x
    paid : Burn.horizon vac+2≤ y
    head : Nonempty (Card D R x y wants (Burn.horizon vac))
set_option quotPrecheck false
variable {x y} (r:Opportunity x y) (Y:Epoch R D x y r)
local notation "X₀"=> (Epoch R D x y r)
local notation "κ"=> Y.vac
local notation "K0"=> Burn.horizon Y.vac
local notation "pr"=> (X.p.profile x)
local notation "Y₀"=> Y.head
namespace Epoch
abbrev data (Y:Epoch R D x y r):= Q.income x y Y.wants r.meet (Burn.horizon Y.vac) Y.paid Y.head
instance : Finite X₀:= by
 let f(u:Epoch R D x y r): Fin (y+1):=⟨u.vac,(by have ht:=u.paid; unfold Burn.horizon at ht; omega)⟩
 refine Finite.of_injective f ?_; rintro ⟨a,h1,h2,h3⟩ ⟨a',h4,h5,h6⟩ hv; have ha:a=a':=congr_arg Fin.val hv; subst a'; rfl
end Epoch
-- finite list of possible loans and their simultaneous k marks at each stage
abbrev Query (u:ℕ):= { i:Loan// i.e ≤ u ∧ i.toll ≤ u }
instance (u:ℕ): Finite (Query u) := by
 let f(i:Query u): Fin (u+1) × Fin (u+1) × Fin (2*u+2):= (⟨i.val.e,Nat.lt_succ_of_le i.prop.1⟩, ⟨i.val.toll,Nat.lt_succ_of_le i.prop.2⟩, ⟨i.val.r, by exact Nat.lt_of_le_of_lt i.val.crest (by obtain ⟨h,h'⟩:=i.prop; omega)⟩)
 refine Finite.of_injective f ?_; rintro ⟨⟨a,b,c,h,h0⟩,hk⟩ ⟨⟨a',b',c',h3,h4⟩,hl⟩ hp; have ha:a=a':=congr_arg (Fin.val ∘ Prod.fst) hp; have hb:b=b':=congr_arg (Fin.val ∘ (Prod.snd ∘ Prod.snd)) hp; have hc:c=c':=congr_arg (Fin.val ∘ (Prod.fst ∘ Prod.snd)) hp; subst a' b' c'; rfl
local notation "tq"=> Query y
abbrev TagData (e n:ℕ):= ((Fin e→ Query n) × Fin e) × Fin (n+1)
-- simplify Sigma binder. Frame proof mask.Shape.Book.Visibility.Scope lengths.
abbrev Tags (n m:ℕ):= Sigma (fun x:Fin (m+1)=> TagData x n)
local instance (n m:ℕ): Finite (Tags n m):= by unfold Tags TagData; infer_instance
namespace Tags
variable {a b:ℕ}(X:Tags a b)
abbrev Datum := Fin X.1.val
def loans : Fin X.1.val→Loan:= fun i=>(X.2.1.1 i).val
abbrev angle : Fin X.1.val:= X.snd.1.2
def order : ℕ:= X.2.2.val
end Tags
open Tags
abbrev Ready (k n s:ℕ)(T:Tags y n): Prop:= Aviary.plusK T.loans univ T.order ≤ Burn.horizon k+2 ∧ T.order+1≤ s
abbrev Ticket (Y:Epoch R D x y r):= {u:Tags y r.count // Ready Y.vac r.count r.stage u}
instance : Finite (Ticket R D r Y):= inferInstanceAs (Finite {u:Tags y r.count // Ready Y.vac r.count r.stage u})
variable (T₁:Ticket R D r Y)
local notation "u"=> T₁.val
-- projections retain literal Fin constants across all uses. Shift geometry receipts fee.V.Selects.Either
abbrev ReleaseR := Publication R D ψ x y Y.wants T₁.val.loans T₁.val.angle T₁.val.order Y.vac (Y.data R D Q r)
def Tolerance (y:ℕ):ℝ:=1/(y+1:ℕ)
def permits (P:ReleaseR R D Q ψ r Y T₁) (t:ℝ) : Prop:= Tuition.Purchased R D ψ x y Y.wants T₁.val.loans T₁.val.angle T₁.val.order Y.vac r.count r.stage (W.μ x y) (p x y) (Z x y) (W.o x y) (Y.data R D Q r) P (Tolerance y) t
-- one pre-L predicate including Occs. Billing isn't exported separately on *all* Ep unrelated R. Need one appointment (shop ready) and true currency.V.
variable {ξv:ℕ→ℕ}
namespace Offices
structure Books where
    lore : ∀ (x y) (r:Opportunity x y) (i:Epoch R D x y r) (k:Ticket R D r i), ReleaseR R D Q ψ r i k
    salary (x y:ℕ)(r:Opportunity x y):Salary G (D.L x)
local notation "B"=> Books R D Q ψ
variable (P':Books R D Q ψ)
structure Bought (t:ℝ) : Prop where
    enroll (i:X₀)(k:Ticket R D r i): permits R D Q W ψ r i k (P'.lore x y r i k) t
    real : SummerS (Z x y) r.count r.stage (p x y) (W.μ x y) (D.L x) (W.o x y) (S x y) (P'.salary x y r) t
structure Sales : Prop where
    later x y (r:Opportunity x y):∀ᶠ t in atTop,Bought R D Q W S ψ r P' t
variable (hK: ∀ i,Poetry.Agenda.Crews R ψ i (D.L i).val)(hO:∀ i j,(Z i j).table=X.O)
include hK hO
-- Z all X.Bank geometries & publication heights constrained by permits. Emit schedule with exact Keeper, not assume exist.
theorem formation (hp:Repeat.Pocket W S)(hw:∀ x,ξv x≤(D.L x).val)(hz:Institute Z ξv):∃ P':Books R D Q ψ,Sales R D Q W S ψ P':=by
 have hC (x y:ℕ)(r:Opportunity x y) (i: Epoch R D x y r) (t:Ticket R D r i) : Nonempty (ReleaseR R D Q ψ r i t):=by haveI:= i.head; apply publishes; exact hK x (Burn.horizon i.vac) (i.paid.trans r.meet.1); exact t.prop.1 -- tactic
 let Y' x y (r:Opportunity x y)(i: Epoch R D x y r)(k:Ticket R D r i):= (hC x y r i k).some
 choose f g using fun x y (r: Opportunity x y)=> hz x y r.meet (D.L x) (hw _) (p x y) _ (W.consumes _ _ r.meet).1 (W.consumes _ _ r.meet).2.1 _ (M x y) (S x y) (hp.price x y r.meet) r.count r.stage r.pos
 let X':= Books.mk (ψ:=ψ) (Q:=Q) Y' f
 refine ⟨X',⟨fun x y r=> ?_⟩⟩; let P:= W.μ x y; have hu (i: Epoch R D x y r) (t:Ticket R D r i):∀ᶠ z in atTop, permits R D Q W ψ r i t (X'.lore x y r i t) z:=by
    haveI : Nonempty (_):= i.head
    exact Tuition.fine R D ψ x y i.wants _ _ _ _ _ _ P _ _ _ (hO x y) _ (X'.lore x y r i t) (Tolerance y) (by unfold Tolerance; positivity) (W.consumes x y r.meet).2.1 t.prop.2
 filter_upwards [g x y r,(eventually_all.mpr fun i=> eventually_all.mpr fun t=> hu i t)] with t h1 h2; exact ⟨h2,h1⟩
end Offices
end YM.QuadraticLocal.Mentor
