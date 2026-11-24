import YM.Integration.WilsonCenteredNestedSigned

/-! Entire signed nested Wilson reading on the original matrix ticket.
Its physical logarithmic exponent precedes the independent order; the
only comparison to buy is the signed value at each comparable vertex. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedLedger
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Log
open Extraction Spec Table Filter Trace.Pilot PhysicalNext.Repeat.Legato
open WilsonCenteredNestedRates WilsonCenteredNestedProgram WilsonCenteredNestedLoggedRow
open WilsonCenteredNestedGross WilsonCenteredNestedSigned
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def debit {n : ℕ} {p : Fin n→Tree} (s : (fork n p).Inner→ℝ) (v : (fork n p).Leaf→S.Tag)
    (D : (fork n p).Inner→ℕ) (m : ℕ) (g : ℝ→ℝ) (z porder : ℕ) (B : ℝ) : ℝ :=
  (premium F Q (fork n p) D s (fun _=>1) * B^(Fintype.card (fork n p).Inner) *
      (∏ i,shell (s i))^z) * s (.inl ())^m * leaves (fork n p) s (degrees v) (s (.inl ())) *
      ∑ i,|g (s i)|^porder

theorem Book {n : ℕ} {p : Fin n→Tree} (s : (fork n p).Inner→ℝ) (v : (fork n p).Leaf→S.Tag)
    (D : (fork n p).Inner→ℕ) (m : ℕ) (g : ℝ→ℝ) (z porder : ℕ) (B : ℝ) :
    WilsonCenteredNestedPhysical.vertexFee F Q s v D m (wage z B) (fun a=>|g a|^porder) =
      debit F Q s v D m g z porder B := by
  unfold WilsonCenteredNestedPhysical.vertexFee debit wage
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Finset.prod_pow]
  ring

/-- One native census, one public Wilson hierarchy at all orders, with
the full originally measured macroscopic spectator and root packet. -/
theorem original (simple : G.Simple) (fac : Facilities R.family f S)
    (l : Ultrafilter (ℕ×ℕ)) (lo : (l : Filter _) ≤ f.fuse)
    (ticket : MatrixTicket (C:=R.family) S F.sector.derivatives (l : Filter _))
    (slow : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (bp : 0 < B)
    (g : ℝ→ℝ) (hg : Coupling G g) {n : ℕ} {p : Fin n→Tree} {I : Type} [Fintype I]
    (v : (fork n p).Leaf→S.Tag) (w : I→S.Tag) (H : ℕ) (D : (fork n p).Inner→ℕ)
    (M η ε δ : ℝ) (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε) (dp : 0 < δ) :
    Nesting.Uniform F Q ∧ LogTrace F Q.port ∧ ∃ (K : ℕ) (C : ℝ),0 ≤ C ∧
    ∀ (J order : ℕ) (A : Rule F Q) (fee : ℝ),0 ≤ fee →
    WilsonCenteredNestedSigned.Signed F Q A g M η order J fee (fork n p) v D H →
    ∃ b : Fin (H+1)→ℝ,(∀j,0 ≤ b j) ∧
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : (fork n p).Inner→ℝ) (z : (fork n p).Plot) (y : I→E4),
      Accept r M η s z → Buffer z y δ →
      (∀ i,|WilsonCenteredNestedActual.amount R simple B g (s i) - 1| < ε) ∧
      ∀ q : Viewers F,‖whole (spectator F q) (Tree.profile z) (voices v) y (voices w) -
        WilsonCenteredNestedViewer.predicted F Q A g v w H D s z y q‖ ≤
      toll (wages v) ε (H+1:ℝ) s + ∑ j : Fin (H+1),∑ c : Q.channels j,
        (bothToll (wages v) ε j D s + debit F Q s v D j g (K+J) order (C+fee)) * (b j * ‖Q.actor j c‖) := by
  obtain ⟨uniform,traced⟩ := WilsonCenteredNestedElection.on_ticket R F Q fac l lo ticket
  obtain ⟨K,C,Cn,docket⟩ := WilsonCenteredNestedSigned.original F Q simple fac.toServices traced.toSingleLog
    g hg Mn ηp (fork n p) v D H
  refine ⟨uniform,traced,K,C,Cn,?_⟩
  intro J order A fee fn signed
  have nonnegative : ∀r,0 ≤ wage (K+J) (C+fee) r := fun r=>
    mul_nonneg (add_nonneg Cn fn) (pow_nonneg (zero_le_one.trans (shell_one r)) _)
  obtain ⟨_,_,b,bn,pan⟩ := WilsonCenteredNestedActual.original R simple F Q fac l lo ticket slow bp g hg
    A _ nonnegative order v w H D M η ε δ Mn ηp ep dp (docket J order A fee fn signed)
  refine ⟨b,bn,?_⟩
  filter_upwards [pan] with r bank
  intro s z y geometry outside
  simpa only [Book] using bank s z y geometry outside

end YM.Integration.WilsonCenteredNestedLedger
