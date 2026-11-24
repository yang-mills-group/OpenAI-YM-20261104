import YM.Integration.WilsonPositionProgramPublicDirectoryGround

/-! At fixed top the finite public frame can be inserted as genuine
single-slot factors in one and the same normalized Wilson moment. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedPivotFields
open Function Finset Lattice XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus
open PowerSeries FVA2 FVA2.Register MS MS.Land MS.Menus MS.Theater Local.Physical
open MS.WilsonBridge.Coupling MS.Book MS.Book.Program
open private sampled from YM.Integration.WilsonPositionBarePointCoefficient
open scoped Classical BigOperators
variable {G:Gauge}{n d:ℕ}(W:Initialize G)(β:Local.Physical.Deck G)(D:Guard G d)

def funds (v:Sec G d)(j:Glyph β d):PowerSeries ℂ :=
  mk fun k=>(Theater.Daylight β d).repr ((coeff k D) v) j

def plant (s:Sample n)(i:Fin n)(v:Sec G d):Bare.Series (W.tree s.F.p) G :=
  ∑j:Glyph β d,Bare.scalar (W.tree s.F.p) (funds β D v j) *
      Rose.regal W d s (chartV s i) (Theater.Daylight β d j)

theorem original (s:Sample n)(v:Tags G d n)(k:ℕ):
    coeff k (Bare.normalized (W.tree s.F.p) G (∏i,plant W β D s i (v i))) =
      Dframe.status D (live W d s) k v := by
  let basis:=Theater.Daylight β d
  let field (a:Fin n→Glyph β d) := numberA W d s (fun i=>basis (a i)) univ
  let part (a:Fin n→Glyph β d)(i:Option (Fin n)) :=
      i.elim (field a) (fun j=>funds β D (v j) (a j))
  have pack : Bare.normalized (W.tree s.F.p) G (∏i,plant W β D s i (v i))=
      ∑a:Fin n→Glyph β d,∏i,part a i := by
    simp only [plant,Fintype.prod_sum,map_sum]
    apply sum_congr rfl
    intro a _
    rw [prod_mul_distrib,show
        (∏ i:Fin n,Bare.scalar (G:=G) (W.tree s.F.p) (funds β D (v i) (a i))) =
           Bare.scalar (W.tree s.F.p) (∏ i,funds β D (v i) (a i)) from
        (map_prod (PowerSeries.map (algebraMap ℂ (Bare.Vertices (W.tree s.F.p) G))) _ univ).symm,
        Bare.normalized_scalar,Fintype.prod_option]
    exact mul_comm _ _
  rw [pack,map_sum,Dframe.seen]
  simp_rw [PowerSeries.coeff_prod]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  have each (i:Fin n):pulseU e D v i=∑j:Glyph β d,
      coeff (e (some i)) (funds β D (v i) j) • basis j :=by
    simp only [funds,coeff_mk]
    exact (basis.sum_repr _).symm
  rw [show pulseU e D v=(fun i=>∑j:Glyph β d,
      coeff (e (some i)) (funds β D (v i) j) • basis j) from funext each]
  simp_rw [MultilinearMap.map_sum,MultilinearMap.map_smul_univ]
  apply sum_congr rfl
  intro a _
  rw [Fintype.prod_option,smul_eq_mul]
  change coeff (e none) (field a)*(∏i,coeff (e (some i)) (funds β D (v i) (a i))) =
      (∏i,coeff (e (some i)) (funds β D (v i) (a i))) * live W d s (e none) (fun i=>basis (a i))
  rw [Rose.lit_up,mul_comm]

variable (Z:WilsonPrescription G){j B:ℕ}(P:Handoff.Directory Z j B)

theorem printed (s:Sample n)(v:Tags G d n)(hs:s.F=Z.run.step j)(k:ℕ)
    (cap:Handoff.Directory.budget G n d+k≤B):
    WilsonPositionOriginalEpochQuadrature.point P d v s.layout k =
      coeff k (Bare.normalized (Z.scheme.tree s.F.p) G
        (∏i,plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) s i (v i))) := by
  rw [sampled P d v s hs k cap,original]

theorem drawn (s:Sample n)(v:Tags G d n)(hs:s.F=Z.run.step j)(q:ℕ)
    (cap:Handoff.Directory.budget G n d+q≤B)(u:ℝ):
    WilsonPositionProgramPublicDirectoryCoin.drawValue Z v q P u s.layout =
      ∑k∈range (q+1),coeff k (Bare.normalized (Z.scheme.tree s.F.p) G
        (∏i,plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) s i (v i)))*(u:ℂ)^k := by
  apply sum_congr rfl
  intro k hk
  rw [printed β Z P s v hs k (by have small:=mem_range.mp hk;omega)]

end YM.Integration.WilsonOriginalPublicPlantedPivotFields
