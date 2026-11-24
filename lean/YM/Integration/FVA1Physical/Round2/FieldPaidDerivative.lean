import YM.Integration.FVA1Physical.Round2.FieldComparedTruncation
import YM.Integration.FVA1Physical.Round2.FieldDerivativeCost

/-! Same-order derivative error for the actual normalized physical insertion.
Both its comparison with a higher truncation and the price of lowering that
truncation are on the identical physical issue and Wilson bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Mosaic MSbar.CrossH MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film
open MSbar.Whisk MSbar.Heath MSbar.Heath.Stock MSbar.Bulk MSbar.Kelvin MSbar.Cacao
open RGComparison.Core16 RGComparison.Core16.Spool Push.Uniform
open YM.Integration.FVA1Physical.Wilson AnalyticBridge.SectorAffine.Offset
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {ι:Type} [Fintype ι]

def fieldReserve (p j:ℕ) := chartInversePower (j+1)+(p+1)
def fieldAuditOrder (p j:ℕ) := p+1+fieldReserve p j*j

theorem paid_field_derivative (J:ι→Lamp G) (A:Issue G) (χ:ChartRatio G) (kind:Kind A.T)
    (branch:A.S.patch.Branches A.S.kernel G) (prem:Premier (main A.f A.pre.clip A.pre.path))
    (crit:Critical A.F A.pre.clip A.pre.path A.ρ) (pd:(mold A.pre A.F A.v).PosDef)
    (vac:Envelope A.pre.eval) (pos:∀ U,0<A.pre.eval U)
    (o:ι→Site A.f) (part:Bool) (b:Site A.c) (Z:Positions (Primary A.c G))
    (l:List (Primary A.c G)) (p s L:ℕ) {D α H y:ℝ} (ha:0≤α) (hZ:‖Z‖≤D)
    (hg:0<A.fClock) (unit:A.fClock≤1) (room:A.fClock*(D+1)≤1)
    (close:∀ i:Slice J,separation (A.S.ratio.embed b) (legs J o i).1 ≤ L*closeN y)
    (hβ:1≤A.pre.beta) (hH:H≤A.pre.beta)
    (large:chartOrderPrice G |A.S.kernel.penalty| (l.length+1) l.length (stencilBound J)+
      ((fieldAuditOrder p l.length+1:ℕ):ℝ) ≤ A.pre.beta)
    (points:∀ z:Positions (Primary A.c G),‖z‖≤D+1 →
      PhysicalFieldComparison J A χ y 1 (fieldAuditOrder p l.length) L part (A.S.ratio.embed b) z)
    (rows:∀ z:Positions (Primary A.c G),‖z‖≤D+1 → ∀ i≤fieldAuditOrder p l.length,
      Vault (MSbar.Measuring.chart A.c G) {b} α s (l.length+1) z
        (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) (fieldAuditOrder p l.length))) H) :
    let Q:=renderedPolynomial (emittedRows A χ (jointFieldBank J A o part) p) p A.fClock
    |buoy (fun z=>expect A.S A.pre (postcard G A.c A.fClock z) (fun U=>look part (tally J o U))
      -clue Q z) Z l| ≤
      (fieldWordConstant (l.length+1) l.length (Nat.lt_succ_self _) +
        ((1+fieldReserve p l.length*l.length:ℕ):ℝ)*H)*A.fClock^(p+1) := by
  let q:=l.length
  let k:=q+1
  let c:=chartInversePower k
  let a:=fieldReserve p q
  let n:=fieldAuditOrder p q
  let d:=1+a*q
  let F:=jointFieldBank J A o part
  let φ:=fun U=>look part (tally J o U)
  let f:=fun z=>expect A.S A.pre (postcard G A.c A.fClock z) φ
  have qk : l.length < k:=Nat.lt_succ_self _
  have budget:c+(p+1+a*l.length)≤a*k:=by
    change c+(p+1+a*q)≤a*(q+1)
    rw [Nat.mul_succ]
    change c+(p+1+a*q)≤a*q+(c+(p+1))
    omega
  have directions:(l.toFinset.image physicalBond).card ≤ q:=
    Finset.card_image_le.trans l.toFinset_card_le
  have rough:=actual_chart_fee A k _ q n (stencilBound_pos J).le directions hβ hH large
  have high:=sparse_field_comparison J A χ branch prem crit pd vac pos o part b Z l k (p+1) a c s L
    qk budget ha hZ hg unit room close points rows rough
  have bound : ‖A.fClock•Z‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg hg.le]
    exact (mul_le_mul_of_nonneg_left (hZ.trans (le_add_of_nonneg_right zero_le_one)) hg.le).trans room
  have field:Envelope φ:=Lumen.Planet.havenreal ((look part).continuous.comp (Spool.tally_cont J o))
  have funds:=reading_chart_order A.S A.pre φ branch vac pos field (stencil_bounded J o part) univ
    (ContinuousLinearMap.id ℝ (Positions (Primary A.c G))) ContinuousLinearMap.norm_id_le
    (fun _ e he=>False.elim (he (mem_univ e))) A.fClock ((abs_of_pos hg).trans_le unit) Z bound k
  have smooth: ContDiffAt ℝ k f Z := (translate_through (f:=f) (z:=Z) funds).smooth
  have eqn:n=p+d:=by dsimp [n,d,fieldAuditOrder,a];omega
  have cutoff:=emitted_prefix A χ F kind pd (show p≤n from eqn ▸ Nat.le_add_right ..)
  have high':|buoy (f-clue (renderedPolynomial (emittedRows A χ F n) (p+d) A.fClock)) Z l| ≤
      fieldWordConstant k q qk*A.fClock^(p+1) := by rw [←eqn];exact high
  have final:=compared_truncation (MSbar.Measuring.chart A.c G) {b} s k p d Z l qk.le f smooth
    (emittedRows A χ F n) (emittedRows A χ F p) hg.le unit ha cutoff
    (fun i _ hi=>rows Z (hZ.trans (le_add_of_nonneg_right zero_le_one)) i (show i ≤ n from hi.trans_eq eqn.symm)) high'
  exact final.trans_eq (by dsimp only [d];ring)

end YM.Integration.FVA1Physical.Round2.Curvature
