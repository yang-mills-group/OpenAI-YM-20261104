import YM.Integration.WilsonCenteredNestedTreeWages
import YM.Integration.WilsonCenteredNestedLedger

/-! A tender at the actual two Wilson couplings on the already elected
tree. Uniform spatial and signed vertex errors stay in separate accounts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeMatched
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree
open Trace.Pilot PhysicalNext.Repeat.Legato
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedProgram WilsonCenteredNestedGross
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedActual WilsonCenteredNestedTreeSharp
open scoped Classical Topology BigOperators
variable {G : Gauge} (R:Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private lemma tax (k:ℕ) (b r a:ℝ) : wage k b r * wage k b a = b^2*(shell r*shell a)^k := by
  rw [mul_pow]
  unfold wage
  ring

private lemma splice {x y z:ℂ} {p E I:ℝ} (pn:0≤p) (left:p*‖x-y‖≤E) (right:p*‖y-z‖≤I) :
    p*‖x-z‖≤E+I := by
  have chain : ‖x-z‖≤‖x-y‖+‖y-z‖ := by
    rw [show x-z=(x-y)+(y-z) by abel]
    exact norm_add_le ..
  apply (mul_le_mul_of_nonneg_left chain pn).trans
  rw [mul_add]
  exact add_le_add left right

theorem original (simple:G.Simple) (fac:Facilities R.family f S) (foundation:Foundation F Q)
    (l:Ultrafilter (ℕ×ℕ)) (lo:(l:Filter _)≤f.fuse)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    (slow:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (bp:0<B) (g:ℝ→ℝ) (hg:Coupling G g)
    (v:full.Leaf→S.Tag) (D m:ℕ) (c:Q.channels m) {M η δ:ℝ} (Mn:0≤M) (ηp:0<η) (dp:0<δ) :
    Nesting.Uniform F Q ∧ LogTrace F Q.port ∧ ∃(J j:ℕ)(K C:ℝ),0≤K ∧ 0≤C ∧
    ∀(k p:ℕ)(A:Rule F Q)(E:ℝ),0≤E→
    WilsonCenteredNestedSigned.Signed F Q A g M η p k E full v (caps m D) m→
    ∀ᶠr:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),Accept r M η (dates r a) z →
    (∀i,|amount R simple B g (dates r a i)-1|<δ) ∧
    charge v m a r * ‖Kernel.output F Q z v c-run F Q A g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩‖ ≤
    K*((shell r*shell a)^J*(a/r)^(D+1)) +
    Fintype.card (Menu.Cut Q D)*((C+E)^2*(shell r*shell a)^(j+k))*(|g r|^p+|g a|^p) := by
  obtain ⟨uniform,logged⟩ := WilsonCenteredNestedElection.on_ticket R F Q fac l lo ticket
  obtain ⟨J,K,Kn,physical⟩ := WilsonCenteredNestedTreeSharp.original F Q fac foundation lo ticket v D m c Mn ηp
  obtain ⟨j,C,Cn,registered⟩ := WilsonCenteredNestedSigned.original F Q simple fac.toServices logged.toSingleLog
    g hg Mn ηp full v (caps m D) m
  refine ⟨uniform,logged,J,j,K,C,Kn,Cn,fun k p A E En enrolled=>?_⟩
  have ln (s:ℝ) : 0≤wage (j+k) (C+E) s :=
    mul_nonneg (add_nonneg Cn En) (pow_nonneg (zero_le_one.trans (shell_one s)) _)
  have paid := WilsonCenteredNestedTreeWages.original F Q A g (wage (j+k) (C+E)) ln p v D m c (registered k p A E En enrolled)
  filter_upwards [physical,paid,currency R simple slow bp g hg (t:=full) dp] with r budget rows current a z ok
  have rp:0<r:=ok.levels.1
  have ap:0<a:=(ok.levels.2.2 (0:Fin 2)).1
  have cash:0≤charge v m a r := by unfold charge WilsonCenteredNestedTreeWallet.toll;positivity
  have localRow:=rows a z ok
  rw [tax] at localRow
  exact ⟨current _ ok.levels,splice cash (budget a z ok) localRow⟩

end YM.Integration.WilsonCenteredNestedTreeMatched
