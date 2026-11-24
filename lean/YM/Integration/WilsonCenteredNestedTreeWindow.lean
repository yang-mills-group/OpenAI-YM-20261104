import YM.Integration.WilsonCenteredNestedTreeMatched
import YM.Integration.WilsonCenteredNestedRunningWindow

/-! Coupling-power error for the complete two-vertex ordinary program on
the original moving separation. The reserve is stated in terms of the
two actual logarithmic expenses of the physical and signed local rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeWindow
open Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree
open Trace.Pilot PhysicalNext.Repeat.Legato PhysMS
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedProgram WilsonCenteredNestedGross
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedActual WilsonCenteredNestedTreeSharp
open scoped Classical Topology BigOperators

private lemma pay {x L Z:ℝ} {q e j:ℕ} (gp:0<x) (gone:x≤1) (ln:0≤L)
    (bill:L*x^4≤Z) (funded:q+4*j≤e) : L^j*x^e≤Z^j*x^q:=by
  calc
    _≤L^j*x^(q+4*j):=mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le gone funded) (pow_nonneg ln _)
    _=(L*x^4)^j*x^q:=by rw [pow_add,pow_mul,mul_pow];ring
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg ln (pow_nonneg gp.le _)) bill _) (pow_nonneg gp.le _)

private lemma product {x l L Z:ℝ} (gp:0<x) (Ln:0≤L) (order:l≤L)
    (cost:L*x^2≤Z) : (l*L)*x^4 ≤ Z^2 :=by
  calc
    _≤(L*L)*x^4:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right order Ln) (pow_nonneg gp.le _)
    _=(L*x^2)^2:=by ring
    _≤_:=pow_le_pow_left₀ (mul_nonneg Ln (sq_nonneg _)) cost _

private lemma dollars {x y:ℝ} (xp:0<x) (yp:0<y) (le:y≤3*x) (p:ℕ) :
    |y|^p+|x|^p≤(3^p+1)*x^p:=by
  rw [abs_of_pos xp,abs_of_pos yp]
  calc
    _ ≤ (3*x)^p+x^p := add_le_add (pow_le_pow_left₀ yp.le le p) le_rfl
    _ = _ := by rw [mul_pow]; ring

variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem original (simple:G.Simple) (fac:Facilities R.family f S) (foundation:Foundation F Q)
    (l:Ultrafilter (ℕ×ℕ)) (lo:(l:Filter _)≤f.fuse)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    (slow:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (bp:0<B) (g:ℝ→ℝ) (hg:Coupling G g)
    (v:full.Leaf→S.Tag) (D m:ℕ) (c:Q.channels m) {M η δ:ℝ} (Mn:0≤M) (ηp:0<η) (dp:0<δ) :
    ∃(J j:ℕ)(K C:ℝ),0≤K ∧ 0≤C ∧
    ∀(k p q b:ℕ)(A:Rule F Q)(E:ℝ),0≤E →
      q+4*J≤b*(D+1) → q+4*(j+k)≤p →
      WilsonCenteredNestedSigned.Signed F Q A g M η p k E full v (caps m D) m →
    let t:=WilsonThermometerWeakPairClock.scale g b
    let Z:=(G.slopeConstant⁻¹+2)^2
    ∀ᶠ a:ℝ in 𝓝[>]0,∀(z:full.Plot),Accept (t a) M η (dates (t a) a) z →
      (∀i,|amount R simple B g (dates (t a) a i)-1|<δ) ∧
      charge v m a (t a) * ‖Kernel.output F Q z v c-
        run F Q A g full (dates (t a) a) z v (caps m D) m ⟨Fin.last m,c⟩‖ ≤
      (K*Z^J+(Fintype.card (Menu.Cut Q D))*((C+E)^2*(3^p+1)*Z^(j+k)))*(g a)^q :=by
  obtain ⟨_,_,J,j,K,C,Kn,Cn,rows⟩ := WilsonCenteredNestedTreeMatched.original R F Q simple fac
    foundation l lo ticket slow bp g hg v D m c Mn ηp dp
  refine ⟨J,j,K,C,Kn,Cn,fun k p q b A E En space accuracy enrolled=>?_⟩
  let t:=WilsonThermometerWeakPairClock.scale g b
  let Z:=(G.slopeConstant⁻¹+2)^2
  let n:ℝ:=Fintype.card (Menu.Cut Q D)
  have nn:0≤n:=by dsimp only [n];positivity
  have geo:0≤n*(C+E)^2:=mul_nonneg nn (sq_nonneg _)
  have late:=WilsonThermometerWeakPairClock.small simple g hg b
  filter_upwards [late.eventually (rows k p A E En enrolled),WilsonCenteredNestedRunningWindow.original simple g hg b,
    (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with a all clock gone z admitted
  obtain ⟨gp,gt,gtle,rate,order,rent⟩:=clock
  obtain ⟨currency,receipt⟩:=all a z admitted
  refine ⟨currency,receipt.trans ?_⟩
  let L:=shell (t a)*shell a
  have rn:0≤ shell a:=zero_le_one.trans (shell_one a)
  have tn:0≤ shell (t a):=zero_le_one.trans (shell_one _)
  have ln:0≤L:=mul_nonneg tn rn
  have paid:L*(g a)^4≤Z:=product gp rn order rent
  have phys:L^J*(a/t a)^(D+1)≤Z^J*(g a)^q:=by
    rw [rate,←pow_mul]
    exact pay gp gone ln paid space
  have marked:L^(j+k)*(|g (t a)|^p+|g a|^p)≤(3^p+1)*Z^(j+k)*(g a)^q:=by
    calc
      _≤L^(j+k)*((3^p+1)*(g a)^p):=mul_le_mul_of_nonneg_left (dollars gp gt gtle p) (pow_nonneg ln _)
      _=(3^p+1)*(L^(j+k)*(g a)^p):=by ring
      _≤(3^p+1)*(Z^(j+k)*(g a)^q):=mul_le_mul_of_nonneg_left (pay gp gone ln paid accuracy) (by positivity)
      _=_:=by ring
  calc
    _=K*(L^J*(a/t a)^(D+1))+(n*(C+E)^2)*(L^(j+k)*(|g (t a)|^p+|g a|^p)):=by
      dsimp only [t,L,n]
      ring
    _≤ K*(Z^J*(g a)^q)+(n*(C+E)^2)*((3^p+1)*Z^(j+k)*(g a)^q):=
      add_le_add (mul_le_mul_of_nonneg_left phys Kn) (mul_le_mul_of_nonneg_left marked geo)
    _=_:=by dsimp only [n,Z];ring

end YM.Integration.WilsonCenteredNestedTreeWindow
