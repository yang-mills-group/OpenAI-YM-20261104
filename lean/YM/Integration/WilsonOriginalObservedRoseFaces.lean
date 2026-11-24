import YM.Integration.WilsonMaxwellThermometerSharedGroundPanel
import YM.Integration.WilsonOriginalObservedRoseGround

/-! Signed seven-face charges at a physical site and an independently chosen ground site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseFaces

open Filter Finset Lattice Wilson Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open XSpace.Photo XSpace.Rose
open Labels XSpace.Tornado XSpace.AxesTangent XSpace.Retirement PhysicalNext.Repeat.Legato Precision
open WilsonPositionThermometerConnected (value)
open WilsonMaxwellThermometerInteracting (first face)
open WilsonMaxwellThermometerFundedSecant (bill)
open WilsonMaxwellThermometerSharedGroundFaces (tree)
open WilsonMaxwellThermometerSharedGroundPanel (change)
open WilsonThermometerPositionTunedGalop (originalRead loss)
open WilsonMaxwellThermometerPublicGalop (quotient node)
open WilsonMaxwellThermometerShiftedPanel (translated)
open scoped Classical BigOperators

abbrev Faces := Finset (Fin 3) → ℂ

def linear (a b : Faces) (t : ℂ) : Faces := fun s=>a s+t*b s

def higher (a b : Faces) (t : ℂ) : ℂ :=
  -(b {0,1}*b {2}+b {0,2}*b {1}+b {1,2}*b {0}) +
  2 * (b {0}*b {1}*a {2} + b {0}*a {1}*b {2} + a {0}*b {1}*b {2} +
    t*b {0}*b {1}*b {2})

theorem expansion (a b : Faces) (t : ℂ) :
    value (linear a b t) = value a + t*first a b + t^2*higher a b t := by
  unfold WilsonPositionThermometerConnected.value linear first higher
  ring

variable {G : Gauge} (R : Run G) (D : ChartRatio G) (W : Initialize G) {V : Store G}
    (x : Sample 3) (p : Tags G 6 3)

/-- All seven signed changes, including the proper faces and their exact cofactors. -/
def unpaid (F ground : Faces) (t : ℂ) : ℂ :=
  let Q:=quotient W (V:=V) x p
  let X:=originalRead R W (V:=V) x p
  let L:=loss R W (V:=V) x p
  ∑s:Finset (Fin 3), (bill F (linear (Q 0) (Q 1) t) s *
      (F s-(X 0 s+t*X 1 s) + (L 0 s+t*L 1 s)) +
    bill (Q 0) ground s * (tree R D W (V:=V) x p s-change R W (V:=V) x p s-ground s))

def remainder (t : ℂ) : ℂ :=
  higher (quotient W (V:=V) x p 0) (quotient W (V:=V) x p 1) t

/-- The signed first node uses the original apparent-field correction at both grades. -/
theorem original (law : LocalRatio D) (F ground : Faces) (t : ℂ) :
    value F - value ground - t*node W (V:=V) x p =
    unpaid R D W (V:=V) x p F ground t + t^2*remainder W (V:=V) x p t := by
  let Q:=quotient W (V:=V) x p
  let S:=linear (Q 0) (Q 1) t
  have move : unpaid R D W (V:=V) x p F ground t =
      (value F-value S)+(value (Q 0)-value ground) := by
    rw [WilsonMaxwellThermometerFundedSecant.signed F S,
      WilsonMaxwellThermometerFundedSecant.signed (Q 0) ground, ←Finset.sum_add_distrib]
    unfold unpaid
    apply Finset.sum_congr rfl
    intro s _
    have a:=WilsonThermometerPositionTunedGalop.face R W (V:=V) x p 0 s
    have b:=WilsonThermometerPositionTunedGalop.face R W (V:=V) x p 1 s
    have c:=WilsonMaxwellThermometerSharedGroundFaces.reported R D W (V:=V) x p law s
    change tree R D W (V:=V) x p s-Q 0 s=change R W (V:=V) x p s at c
    rw [←a,←b,←c]
    dsimp only [S,linear,Q]
    ring
  rw [move]
  have cap:=expansion (Q 0) (Q 1) t
  change value S = value (Q 0)+t*first (Q 0) (Q 1)+t^2*remainder W (V:=V) x p t at cap
  change value F-value ground-t*first (Q 0) (Q 1) = _
  linear_combination cap

def fine (m : Mesh) (o : m.Tuple (n:=3)) (p : Tags G 6 3) : Faces :=
  face (live W 6 (translated m (Mesh.back m o)) 0) p

theorem heard (m : Mesh) (o : m.Tuple (n:=3)) (p : Tags G 6 3) :
    value (fine W m o p) = WilsonMaxwellThermometerIncidenceSmearing.read W m o p := rfl

end YM.Integration.WilsonOriginalObservedRoseFaces
