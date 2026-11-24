import YM.FVAAlt2.Periodic.Primary
import YM.RegulatorIR.Older.Trunk
/-!
# Full finite-period copy of the primitive kernels of the genuine analytic patch step

Uses exact `Sphere` which TOP estimator actually runs, no parity winding modifications.
 Scroll here is POSITIVE ORIENTATION timbers, factor one on both sums, with no divided right-tag. Lift supports only after selecting the relative.D.Boss. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth
open Function Finset MeasureTheory Filter Set Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Deck Motion Prim PertExtension Chart Lattice Tree Gauge Binding Diagram Diagram.Formal RG Wilson Oracle
open FreeResolvent (flatten Slot PAC)
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix Matrix.Norms.Frobenius
variable {c f n:Side}{G: Gauge}
variable {J I:Type} {k u r:ℕ}
-- ℝ Kernel coordinates in actual chart
abbrev Pin (n:Side)(G:Gauge):= FreeResolvent.Slot G n 1
abbrev Pins (f c:Side)(G:Gauge):= (Pin f G)⊕ (Pin c G)
def imprint (G:Gauge)(n:Side): Foot G→ Pin n G:= (linksQ G).swrap n
def joint (G:Gauge)(f c:Side): KFoot G→ Pins f c G:= Sum.map (imprint G f) (imprint G c)
def skate (e:I→J)(v:Tuple I r) : Tuple J r:= e ∘ v
-- W.Scoped additive terms project (roots fixed prevents determinant mistakes)
def harvest (e:I→J)(T:Packet I r): Packet J r:= Stalk.collect (skate e) T
lemma retired_zero (e:I→J): harvest e (0:Packet I r)=0:=by ext1 j; exact tsum_zero
lemma inflates (e:I→J) {T:Packet I r}(h:Prim.Bounded T) (v:J→ℝ):strum (harvest e T) v=strum T (v ∘ e):=by
    let U(x:Tuple I r):= T x * noodle (v ∘ e) x
    have hx:Summable U:= summable_of_hasFiniteSupport (Set.Finite.subset h (by intro x hx;contrapose! hx;change ¬U x≠0; rw [not_not]; unfold U; rw [Function.notMem_support.mp hx];ring))
    unfold strum; rw [show _= ∑' i,U i from rfl] -- wrong occurrence.
    rw [← Stalk.collected_sum (skate e) hx]; apply tsum_congr;intro x
    unfold harvest Stalk.collect; rw [← tsum_mul_right]; apply tsum_congr; intro u; rw [← show noodle v (skate e u.val)=noodle v x from congr_arg (noodle v) u.property];rfl
lemma takes_s (e:I→J)(T:Packet I r)(ht:Packet.IsSym T): Packet.IsSym (harvest e T) :=by
    intro p k
    let f : Stalk (skate (r:=r) e) k ≃ Stalk (skate (r:=r) e) (k ∘ p) := Equiv.subtypeEquiv (Tuple.perm I p) (fun x=> ((Tuple.perm J p).injective.eq_iff (a:=skate e x) (b:=k)).symm )
    unfold harvest Stalk.collect; rw [← f.tsum_eq (fun i=> T i.val)]; exact tsum_congr (fun x=> ht p x.val)
variable [Fintype J]
lemma finish (e:I→J)(T:Ranked I)(h:∀ i,Prim.Bounded (T i)) (k:ℕ)(v:J→ℝ): MvPolynomial.eval v (packed (fun i=> harvest e (T i)) k)=drums T k (v ∘ e):=by
    rw [← speaking]; unfold drums; simp_rw [fun i=> inflates e (h i) v]
lemma workOrder {J'} (S':Finset J')(T:J'→Orders I)(h: ∀ j∈S', Vacuum (T j)): Vacuum (∑ i∈S', T i):= by
    intro r i hr; rw [Finset.sum_apply,Finset.sum_apply] at hr; obtain ⟨j,hj,he⟩:= exists_ne_zero_of_sum_ne_zero hr; exact h j hj _ _ he

def sendL (e:I→J) (T:Orders I):Orders J:=fun j v=> harvest e (T j v)
omit [Fintype J] in
lemma within {T:Ranked I} (e:I→J)(h:Within k T): Within k (fun i=> harvest e (T i)):= fun i hi=> h i (fun hh=>hi (by dsimp only; rw [hh,retired_zero]))
omit [Fintype J] in
lemma known (e:I→J) {T:Orders I}(h:gradedSymmetric T): gradedSymmetric (sendL e T):=fun i j=> takes_s e _ (h i j)
omit [Fintype J] in
lemma used (e:I→J){T:Orders I}(h:Vacuum T): Vacuum (sendL e T):=by
    intro r i he; apply h r i; intro hv; apply he; unfold sendL; rw [hv,retired_zero]
lemma costK (e:I→J) {T:Orders I}(h: Vacuum T) (hv:∀ k r, Bounded (T k r))(k:ℕ)(x:J→ℝ): PowerSeries.coeff k (flavor 2 x (sendL e T))=drums (T k) (k+2) (x∘ e):= ( flavor_lo .. ).trans ( finish e (T k) (hv k) _ x )
lemma payRoot (e:I→ J){p: Micro I}{s:ℝ}{T:Orders I}(u:ℕ) (hu:u≤2) (h:Lab u s p T) (k:ℕ)(hk:0<k) (x:J→ℝ): PowerSeries.coeff k (flavor 2 x (sendL e T))=s*PowerSeries.coeff (k+u) (tale (flank p (x ∘ e))):=by
    rw [flavor_lo]; unfold sendL; rw [← pack_extends (within e (h.scope_ k)) (m:=k+2) (by omega),finish e _ (h.sized k)]; exact h.figures _ hk
open PowerSeries
variable {N:Binding.Scale} {S:StepData c f}
abbrev topR (c f:Side):= Sum (Edge (Site f)) (Edge (Site c))
def hop (n:Side)(p:Edge (Site n)):Edge Cover:= ( Lattice.lift p.1,p.2)
def traverse (c f:Side) : topR c f→ Branchix:= Sum.map (hop f) (hop c)
def studied (T: Branchix→ Orders (KFoot G))(f c:Side): Orders (Pins f c G) :=∑ i: topR c f, sendL (joint G f c) (T (traverse c f i))
variable {T:Branchix→Orders (KFoot G)} {F: Forest S.ratio} (hs: Sphere S F N T)
include hs
lemma ranked_root (x) : Vacuum (T x):= by rcases x with x|x; all_goals exact (hs _).form (by first | exact Nat.zero_le _|exact le_refl _)
lemma paying : Vacuum (studied T f c) := workOrder _ _ ( fun i _=> used _ (ranked_root hs _) )
lemma knowledge : gradedSymmetric (studied T f c):= by
   intro i j; unfold studied; rw [ Finset.sum_apply, Finset.sum_apply ]; exact symmetric_sum (fun k _ => known (joint G f c) ( hs (traverse c f k) |>.smooth ) i j )
omit hs in lemma flavor_sum {Y: Type} (S: Finset Y)(T:Y→ Diagram.Orders J) (v:J→ℝ)(b:ℕ) : flavor b v (∑ i∈S,T i) = ∑ i∈S, flavor b v (T i) := by
   ext1 i; simp_rw [map_sum,flavor_lo,Finset.sum_apply,pack_sum,map_sum]
local notation "P"=> joint G f c
lemma aced (e:ℕ)(h:0<e) (x:Pins f c G→ℝ) : coeff e (flavor 2 x (studied T f c))= ∑ k: topR c f, let u:=traverse c f k; dry u * coeff (e+barkN u) (tale (flank (prism S F N u) (x ∘ joint G f c))):= by
   unfold studied; rw [flavor_sum,map_sum]; apply sum_congr rfl; intro i _; apply payRoot _ _ _ (hs _) e h
   cases i <;> first| exact Nat.zero_le _|exact le_refl _
end YM.RegulatorIR.FVAAlt2.Booth
