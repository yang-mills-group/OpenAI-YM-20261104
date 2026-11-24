import YM.Integration.WilsonPositionProgramPublicIntrinsicAxes

/-! The actual independent stopped publication on every field in a
finite cohort, after restoring both arriving field changes and all grades. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicDirectoryTensor
open Filter Set Finset Function Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Menus PowerSeries Lattice
open Local.Physical
open WilsonPositionRawEpoch WilsonPositionProgramPublicDirectoryCoin
open scoped BigOperators Classical Topology
variable {G:Gauge}{Z:WilsonPrescription G}{i budget n:ℕ}(P:Handoff.Directory Z i budget)
    (d:ℕ)(x:pack n)

def grade (k:ℕ):Point G d n:=
  ∑ a∈tally k n,∑ t,coeff (a none) (P.point_fk n d t x) •
    (Dframe.each t).compLinearMap (fun j=>coeff (a (some j)) (matrix Z i d))

theorem deposited (k:ℕ)(v:Tags G d n):
    grade P d x k v=WilsonPositionOriginalEpochQuadrature.point P d v x k:=by
  simp only [grade,WilsonPositionOriginalEpochQuadrature.point,_root_.sum_apply,
    _root_.smul_apply,MultilinearMap.compLinearMap_apply,smul_eq_mul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro t _
  exact mul_comm ..

def programme (q:ℕ)(u:ℝ):Point G d n:=
  ∑ k∈range (q+1),(u:ℂ)^k • grade P d x k

theorem read (q:ℕ)(u:ℝ)(v:Tags G d n):
    programme P d x q u v=drawValue Z v q P u x:=by
  simp only [programme,drawValue,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,deposited]
  apply sum_congr rfl
  intro k _
  exact mul_comm ..

variable (B:Deck G)
local notation "Γ" => Glyph B d

def filed (w:Fin n→Γ→ℂ):Tags G d n:=fun j=>∑ a,w j a • Theater.Daylight B d a

theorem original (q:ℕ)(u:ℝ)(w:Fin n→Γ→ℂ):
    drawValue Z (filed d B w) q P u x=∑ a:Fin n→Γ,(∏j,w j (a j))*
       drawValue Z (fun j=>Theater.Daylight B d (a j)) q P u x:=by
  rw [←read]
  unfold filed
  rw [MultilinearMap.map_sum]
  apply sum_congr rfl
  intro a _
  rw [MultilinearMap.map_smul_univ,smul_eq_mul,read]

end YM.Integration.WilsonPositionProgramPublicDirectoryTensor
