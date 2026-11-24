import YM.QuadraticLocal.Mentor.Camp
/-!
 # Credential. Bind Press to this formal URI, BEFORE any orientations

 Forecast (pre-geometry) incomes uniform across all opportunity count & height
 at a given stage. The Credited sum is on *actual Roll lengths, including
 all roots and their genuine wires*, so annual estimates take place on the
 given history, not assuming some old geometry elsewhere. Can carry using
 Monitor & delay adjustments.Let µ boundary paid. Does not infer readiness for
 ALL subsequent demands in sharper aesthetics; teacher clocks verify all finitely
 many polynomials costs to be used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
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
namespace Mentor
variable {G:Gauge} {X: Metals G}
variable (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (D:Rolls X.p) (Q:R.Tab D)
variable (φ:ℕ→ℕ) (K0:Offices.Books R D Q φ)
set_option quotPrecheck false
open QuadraticLocal.Mentor
namespace Port
variable {x y:ℕ}
local notation "L"=> (D.L x)
local notation "E"=> QuadraticLocal.Mentor.Epoch R D x y
local notation "W"=> (Opportunity x y)
local notation "Pnt"=> QuadraticLocal.Mentor.Ticket R D
private lemma venture_sum {ι:Type} (s:Finset ι)(f:ι→ℝ→ℝ){K:Side}(h:∀i∈s,Reserve G K (f i)): Reserve G K (fun y=>∑ i∈s,f i y):= by
 induction s using Finset.induction with
 | empty=> simp only [Finset.sum_empty]; exact Reserve.const _
 | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h _ (mem_insert_self ..)).add (ih fun k hk=>h k (mem_insert_of_mem hk))
private lemma capitals {ι:Type}[Finite ι]{L':Side} (f:ι→ℝ→ℝ)(h:∀ i,Reserve G L' (f i)) (he:∀ i t,0≤f i t): ∃ g:ℝ→ℝ,Reserve G L' g ∧ (∀ t,0<g t) ∧ (∀ i t,f i t ≤ g t):=by
 letI:= Fintype.ofFinite ι; refine ⟨fun x=>1+∑ i:ι,f i x,(Reserve.const _).add (venture_sum _ f (fun i _=>h i)),fun t=> add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _=>he ..),fun i t=>?_⟩; exact le_trans (Finset.single_le_sum (f:=fun i=>f i t) (fun i _=>he i t) (Finset.mem_univ i)) (le_add_of_nonneg_left zero_le_one)

variable (x y)
abbrev Cashpoint := Σ o:Opportunity x y, Σ p:Epoch R D x y o, Σ t:QuadraticLocal.Mentor.Ticket R D o p, Fin (t.val.order+1)
local instance : Finite (Cashpoint R D x y):=by unfold Cashpoint; infer_instance
local notation "Y"=> Cashpoint R D x y
variable (v:Cashpoint R D x y)
local notation "Π"=> v.snd.snd.fst
local notation "q"=> v.snd.fst
local notation "pT"=> (Π).val
local notation "Ht"=> (pT).angle
local notation "A"=> (Params R D φ x y (q).wants (pT).loans (q).vac)
local notation "S"=> ((K0).lore x y v.fst q Π)
local notation "k"=> v.snd.snd.snd.val
-- Wall payment, affine.Approval.Hidden.C uses fide.Real.Rag.Field.Time.Scales
protected def LoanAt (u:ℝ)(b:ℝ): Prop:= ∀ (i:A), i.1.self.paid=ConnectedActivityE6.loopBill G (D.L x) u→ ((S).atoms k i).Faith univ Ht (QuadraticLocal.Poetry.Agenda.guard (pT).loans univ k) (QuadraticLocal.Poetry.Agenda.waist R (Burn.horizon (q).vac) x) b
-- locate namespace Pt
local notation "b₀"=> Port.LoanAt
lemma loan_rank : ∃ f:ℝ→ℝ,Reserve G (D.L x) f ∧ (∀ i,0≤ f i) ∧ ∀ i:ℝ,Port.LoanAt R D Q φ K0 x y v i (f i):=by
 haveI: Nonempty (_):= (q).head
 obtain ⟨f,hf,hq,hH⟩:= Publication.earn (S) k (show k≤(pT).order from Nat.le_of_lt_succ v.snd.snd.snd.prop); exact ⟨f,hf,hq,fun i j he=> hH _ _ he⟩
lemma widen {a b t:ℝ}(h:Port.LoanAt R D Q φ K0 x y v t a)(hp:a≤b): Port.LoanAt R D Q φ K0 x y v t b:= fun i he=> ⟨(h i he).pinned,budget_loosen (h i he).price hp⟩
end Port
structure Forecast where
 cost : ℕ→ℕ→ℝ→ℝ
 higher x y i : 0 < cost x y i
 reserve x y: RemainderComparison.Reserve G (D.L x) (cost x y)
 faith x y i t: Port.LoanAt R D Q φ K0 x y t i (cost x y i)
lemma speculate : Nonempty (Forecast R D Q φ K0):=by
 have H x y: ∃ (f:ℝ→ℝ),Reserve G (D.L x) f∧(∀ t,0<f t)∧∀ (v:Port.Cashpoint R D x y) t, Port.LoanAt R D Q φ K0 x y v t (f t):=by
    choose f hf he h using fun v:Port.Cashpoint R D x y=> Port.loan_rank R D Q φ K0 x y v; obtain ⟨g,hg,hE,hP⟩:= Port.capitals f hf he; exact ⟨g,hg,hE,fun v t=>Port.widen R D Q φ K0 x y v (h v _) (hP v t)⟩
 choose f hf hF h using H; exact ⟨f,hF,hf,fun x y i t=> h x y t i⟩
end Mentor
end YM.QuadraticLocal
