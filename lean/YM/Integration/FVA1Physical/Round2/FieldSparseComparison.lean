import YM.Integration.FVA1Physical.Round2.FieldSliceOrder
import YM.Integration.FVA1Physical.Round2.FieldWordSlice
import YM.Integration.FVA1Physical.Round2.FormalFieldOrder
import YM.Integration.FVA1Physical.Round2.FormalFieldTruncation
import YM.Integration.FVA1Physical.Round2.FieldDerivativeReserve
import YM.Integration.FVA1Physical.Round2.FieldSharpSeason

/-! A high-order comparison of actual Haar readings with the independent
finite Wilson polynomial buys lower-order derivatives on any sparse test.
The explicit rough derivative cost is polynomial in the inverse coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Mosaic MSbar.CrossH MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film
open MSbar.Whisk MSbar.Heath MSbar.Heath.Stock MSbar.Bulk MSbar.Kelvin
open RGComparison.Core16 RGComparison.Core16.Spool Push.Uniform
open YM.Integration.FVA1Physical.Wilson AnalyticBridge.SectorAffine.Offset
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {ι : Type} [Fintype ι]

def fieldWordConstant (k j : ℕ) (hj : j < k) : ℝ := (field_derivative_reserve k j hj).choose

theorem sparse_field_comparison (J : ι→Lamp G) (A : Issue G) (χ : ChartRatio G)
    (branch : A.S.patch.Branches A.S.kernel G)
    (prem : Premier (main A.f A.pre.clip A.pre.path)) (crit : Critical A.F A.pre.clip A.pre.path A.ρ)
    (pd : (mold A.pre A.F A.v).PosDef) (vac : Envelope A.pre.eval) (pos : ∀ U,0<A.pre.eval U)
    (o : ι→Site A.f) (part : Bool) (b : Site A.c) (Z : Positions (Primary A.c G))
    (l : List (Primary A.c G)) (k p a c s L : ℕ) (hj : l.length < k)
    (high : c+(p+a*l.length) ≤ a*k) {D α H y : ℝ} (ha : 0≤α) (hZ : ‖Z‖≤D)
    (hg : 0<A.fClock) (unit : A.fClock≤1) (room : A.fClock*(D+1)≤1)
    (close : ∀ i:Slice J,separation (A.S.ratio.embed b) (legs J o i).1 ≤ L*closeN y)
    (points : ∀ z:Positions (Primary A.c G), ‖z‖≤D+1 →
      PhysicalFieldComparison J A χ y 1 (p+a*l.length) L part (A.S.ratio.embed b) z)
    (rows : ∀ z:Positions (Primary A.c G), ‖z‖≤D+1 → ∀ i ≤ p+a*l.length,
      Vault (MSbar.Measuring.chart A.c G) {b} α s k z
        (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) (p+a*l.length))) H)
    (rough : chartOrderPrice G (A.pre.beta*A.S.kernel.penalty) k (l.toFinset.image physicalBond).card (stencilBound J) +
       (((p+a*l.length+1:ℕ):ℝ)*H) ≤ (A.fClock⁻¹)^c) :
    let n:=p+a*l.length
    let Q:=renderedPolynomial (emittedRows A χ (jointFieldBank J A o part) n) n A.fClock
    |buoy (fun z=>expect A.S A.pre (postcard G A.c A.fClock z) (fun U=>look part (tally J o U))
        -clue Q z) Z l| ≤ fieldWordConstant k l.length hj * A.fClock^p := by
  let g:=A.fClock
  let n:=p+a*l.length
  let bank:=jointFieldBank J A o part
  let Q:=renderedPolynomial (emittedRows A χ bank n) n g
  let φ:=fun U=>look part (tally J o U)
  let f:=fun z=>expect A.S A.pre (postcard G A.c g z) φ
  let K:=l.toFinset
  let P:=coordinateProjection K
  let err:=fun z=>f z-clue Q z
  have field : Envelope φ := Lumen.Planet.havenreal ((look part).continuous.comp (Spool.tally_cont J o))
  have cap:=stencil_bounded J o part
  have u : |g|≤1 := (abs_of_pos hg).trans_le unit
  have small {w:Positions (Primary A.c G)} (hw:‖w‖≤D+1) : ‖g•w‖≤1 := by
    rw [norm_smul,Real.norm_of_nonneg hg.le]
    exact (mul_le_mul_of_nonneg_left hw hg.le).trans room
  have throughZ:=reading_chart_order A.S A.pre φ branch vac pos field cap univ
    (ContinuousLinearMap.id ℝ (Positions (Primary A.c G))) ContinuousLinearMap.norm_id_le
    (fun _ e he=>False.elim (he (mem_univ e))) g u Z (small (hZ.trans (le_add_of_nonneg_right zero_le_one))) k
  have trueSmooth : ContDiffAt ℝ k f Z := (translate_through (f:=f) (z:=Z) throughZ).smooth
  apply coordinate_word_bound err Z l ((trueSmooth.sub (helm Q k).contDiffAt).of_le (Nat.cast_le.mpr hj.le))
  apply (field_derivative_reserve k l.length hj).choose_spec.2 _ _ 0 a c p g hg unit high
  intro w hw
  rw [add_zero]
  let z:=Z+P w
  have hz : ‖z‖≤D+1 := (norm_add_le ..).trans (add_le_add hZ ((P.le_opNorm w).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (projection_contract K)).trans (hw.trans (pow_le_one₀ hg.le unit)))))
  have physical:=physical_slice_at A.S A.pre φ branch vac pos field cap K g u Z w (small hz) k
  have monies:=represented_trunk (MSbar.Measuring.chart A.c G) {b} z s k n (emittedRows A χ bank n)
    hg.le unit (rows z hz)
  have formal:=affine_chart_bound P (projection_contract K) Z w
    (vaulted_operator (MSbar.Measuring.chart A.c G) {b} ha s k z Q monies)
  refine ⟨physical.smooth.sub formal.smooth,?_,?_⟩
  · change ‖iteratedFDeriv ℝ k ((fun v=>f (Z+P v))-(fun v=>clue Q (Z+P v))) w‖ ≤ _
    rw [iteratedFDeriv_sub_apply physical.smooth formal.smooth]
    exact (norm_sub_le ..).trans ((add_le_add (physical.pay k le_rfl) (formal.pay k le_rfl)).trans rough)
  · have value:=(points z hz) o close
    change |f z - taste n (bulkColumn A χ (g•z) bank n) g|≤g^((n:ℝ)+1-1) at value
    rw [←rendered_emitted A χ bank n branch prem crit pd hg.ne' z,add_sub_cancel_right,Real.rpow_natCast] at value
    exact value

end YM.Integration.FVA1Physical.Round2.Curvature
