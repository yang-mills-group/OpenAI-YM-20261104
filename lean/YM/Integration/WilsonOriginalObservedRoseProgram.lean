import YM.Integration.WilsonOriginalObservedRoseCoarse

/-! All thermal coefficients of the seven original positioned faces on the
fitted finite cells. The correction acts inside each face before multiplication. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseProgram
open Function Filter Finset PowerSeries RG Lattice Wilson PhysicalNext.Repeat.Legato
open Maxwell XSpace XSpace.Rose XSpace.Cirrus XSpace.Photo XSpace.Normalize XSpace.Structure1
open WilsonPositionThermometerConnected (value)
open WilsonMaxwellThermometerPublicGalop (quotient)
open WilsonMaxwellThermometerInteracting (first)
open WilsonThermometerPositionTunedGalop (originalRead loss)
open WilsonSeparatedOriginalThermometerCells (weight positions)
open WilsonOriginalObservedRoseJoint (locations lowerSite)
open WilsonMaxwellThermometerPublicStation (report)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)
    (x:Sample 3)(p:Tags G 6 3)

def face (s:Badge) : PowerSeries ℂ := PowerSeries.mk (fun e=>quotient W (V:=V) x p e s)

theorem original_face (s:Badge) :
    face W (V:=V) x p s=PowerSeries.mk (fun e=>originalRead R W (V:=V) x p e s)-
      PowerSeries.mk (fun e=>loss R W (V:=V) x p e s):=by
  apply PowerSeries.ext
  intro e
  rw [face,map_sub,coeff_mk,coeff_mk,coeff_mk]
  have h:=WilsonThermometerPositionTunedGalop.face R W (V:=V) x p e s
  linear_combination -h

def entry:PowerSeries ℂ:=Rose.b3 (face W (V:=V) x p)

theorem constant : coeff 0 (entry W (V:=V) x p)=value (quotient W (V:=V) x p 0):=by
  simp [entry,Rose.b3,value,face,coeff_zero_eq_constantCoeff,Algebra.smul_def]

theorem slope : coeff 1 (entry W (V:=V) x p)=WilsonMaxwellThermometerPublicGalop.node W (V:=V) x p:=by
  rw [entry,WilsonMaxwellThermometerInteracting.coefficient]
  simp only [face,coeff_mk,WilsonMaxwellThermometerPublicGalop.node]

def board (k:ℝ→ℕ)(r:ℝ)(z:ℕ×ℕ)(tags:Tags G 6 3):PowerSeries ℂ:=
  if live:k r≤z.1 then
    ∑o:locations R z,PowerSeries.C (weight (Rose.test K) (positions (R:=R) r z) o)*
      entry W (V:=V) (lowerSite R (k r) r z live o) tags
  else 0

theorem heard (k:ℝ→ℕ)(r:ℝ)(z:ℕ×ℕ)(tags:Tags G 6 3)(e:ℕ)(live:k r≤z.1):
    coeff e (board R W K k r z tags)=∑o:locations R z,weight (Rose.test K) (positions (R:=R) r z) o*
      coeff e (entry W (V:=V) (lowerSite R (k r) r z live o) tags):=by
  simp only [board,dif_pos live,map_sum,coeff_C_mul]

theorem first_order (k:ℝ→ℕ)(r:ℝ)(z:ℕ×ℕ)(tags:Tags G 6 3):
    coeff 1 (board R W K k r z tags)=report R W K k r z tags:=by
  by_cases live:k r≤z.1
  · rw [heard R W K k r z tags 1 live,report,dif_pos live]
    simp_rw [slope]
    rfl
  · simp only [board,report,dif_neg live,map_zero]

end YM.Integration.WilsonOriginalObservedRoseProgram
