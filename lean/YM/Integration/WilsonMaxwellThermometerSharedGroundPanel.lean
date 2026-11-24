import YM.Integration.WilsonMaxwellThermometerSharedGroundFaces
import YM.Integration.WilsonMaxwellThermometerFundedSecant

/-! Keep the complete conditional Gaussian face, each proper cofactor, the
common elected inversion and the native regulator section on the same node. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSharedGroundPanel
open Filter Function Set Finset Lattice Wilson Labels Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Photo
open XSpace.Tornado XSpace.AxesTangent XSpace.Retirement XSpace.Rose PhysicalNext.Repeat.Legato Precision
open WilsonThermometerPositionTunedPublicCharge WilsonMaxwellThermometerInteracting
open WilsonPositionThermometerConnected WilsonMaxwellThermometerFundedSecant
open WilsonMaxwellThermometerReleasedSection (cells)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(D:ChartRatio G)(W:Initialize G){V:Normalize.Store G}(x:Sample 3)(p:Tags G 6 3)

def change (S:Badge):ℂ:=PowerSeries.coeff 0 (WilsonThermometerPositionTunedPublicCharge.signed R W 6 x
  (pulseU (0:Days 3) (deck (V.layout W (grab x) 6)) p) S)

def withdrawal (F:Badge→ℂ):ℂ:=
  let Q:=WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p 0
  let X:=WilsonMaxwellThermometerSharedGroundFaces.tree R D W (V:=V) x p
  ∑ s:Badge,bill F Q s * (F s-X s+change R W (V:=V) x p s)

theorem node (law:LocalRatio D)(F:Badge→ℂ):
    value F-value (WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p 0)=
      withdrawal R D W (V:=V) x p F:=by
  rw [WilsonMaxwellThermometerFundedSecant.signed]
  apply Finset.sum_congr rfl
  intro s _
  apply congrArg (_ * ·)
  exact (show _ from (by
    unfold change
    rw [←WilsonMaxwellThermometerSharedGroundFaces.reported R D W x p law s]
    ring))

theorem price (law:LocalRatio D)(F:Badge→ℂ)(δ:Badge→ℝ)
    (paid:∀s,‖F s-WilsonMaxwellThermometerSharedGroundFaces.tree R D W (V:=V) x p s‖≤δ s):
    let Q:=WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p 0
    ‖value F-value Q‖ ≤ ∑s:Badge,‖bill F Q s‖ * (δ s + ‖change R W (V:=V) x p s‖):=by
  dsimp only
  rw [node R D W x p law,withdrawal]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _=>?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (paid s) le_rfl)) (norm_nonneg _)

variable (K:Rose.Pick V)(k:ℝ→ℕ)

theorem original (law:LocalRatio D)(r:ℝ)(z:ℕ×ℕ)(F:Sample 3→Badge→ℂ):
    cells R K k r z (fun x=>value (F x)) -
        cells R K k r z (fun x=>value (WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p 0)) =
      cells R K k r z (fun x=>withdrawal R D W (V:=V) x p (F x)):=by
  by_cases h:k r≤z.1
  · simp only [cells,dif_pos h,←sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro o _
    rw [←smul_sub,node R D W _ p law]
  · simp only [cells,dif_neg h,sub_zero]

end YM.Integration.WilsonMaxwellThermometerSharedGroundPanel
