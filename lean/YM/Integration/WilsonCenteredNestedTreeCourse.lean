import YM.Integration.WilsonCenteredNestedTreeLocalRows
import YM.Integration.WilsonCenteredNestedActual

/-! The measured sharp fork and its two independently priced vertex edits
on one elected original Wilson hierarchy at both literal running couplings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeCourse
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree OPE.Nesting.Composite
open Trace.Pilot PhysicalNext.Repeat.Legato
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedProgram WilsonCenteredNestedTreeLocalRows
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedActual WilsonCenteredNestedTreeSharp
open scoped Classical Topology BigOperators
variable {G : Gauge} (R:Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private lemma splice {x y z:ℂ} {p E h:ℝ} (pn:0≤p) (left:p*‖x-y‖≤E) (right:‖y-z‖≤h) :
    p*‖x-z‖≤E+p*h := by
  have loc : ‖x-z‖≤‖x-y‖+‖y-z‖ := by rw [show x-z=(x-y)+(y-z) by abel];exact norm_add_le ..
  apply (mul_le_mul_of_nonneg_left loc pn).trans
  rw [mul_add]
  exact add_le_add left (mul_le_mul_of_nonneg_left right pn)

theorem original (simple:G.Simple) (fac:Facilities R.family f S) (foundation:Foundation F Q)
    (l:Ultrafilter (ℕ×ℕ)) (lo:(l:Filter _)≤f.fuse)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    (slow:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (bp:0<B) (g:ℝ→ℝ) (hg:Coupling G g)
    (v:full.Leaf→S.Tag) (D m:ℕ) (c:Q.channels m) {M η δ:ℝ} (Mn:0≤M) (ηp:0<η) (dp:0<δ) :
    Nesting.Uniform F Q ∧ LogTrace F Q.port ∧ ∃(J:ℕ)(K:ℝ),0≤K ∧ ∀ᶠr:ℝ in 𝓝[>]0,
    ∀(a:ℝ)(z:full.Plot),Accept r M η (dates r a) z →
    (∀i,|amount R simple B g (dates r a i)-1|<δ) ∧
    ∀(A:Rule F Q)(e h:Menu.Cut Q D→ℝ),
      (∀t,‖innerValue F Q (measured F Q) g v z a t-innerValue F Q A g v z a t‖≤e t) →
      (∀t,‖outerValue F Q (measured F Q) g v z r m c t-outerValue F Q A g v z r m c t‖≤h t) →
      charge v m a r * ‖Kernel.output F Q z v c-run F Q A g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩‖ ≤
      K*((shell r*shell a)^J*(a/r)^(D+1)) + charge v m a r * invoice F Q A g r a v z D m c e h := by
  obtain ⟨whole,logged⟩ := WilsonCenteredNestedElection.on_ticket R F Q fac l lo ticket
  obtain ⟨J,K,Kn,physical⟩ := WilsonCenteredNestedTreeSharp.original F Q fac foundation lo ticket v D m c Mn ηp
  refine ⟨whole,logged,J,K,Kn,?_⟩
  filter_upwards [physical,currency R simple slow bp g hg (t:=full) dp] with r held current a z ok
  refine ⟨current _ ok.levels,fun A e h child parent=>?_⟩
  have rp : 0<r := ok.levels.1
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have paid : 0≤charge v m a r := by unfold charge WilsonCenteredNestedTreeWallet.toll;positivity
  exact splice paid (held a z ok) (priced F Q A g r a v z D m c e h child parent)

end YM.Integration.WilsonCenteredNestedTreeCourse
