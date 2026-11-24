import YM.Integration.WilsonMaxwellThermometerInheritedCells
import YM.XSpace.Galop

/-! The original all-offset public thermometer evaluated on its seven finite normalized Wilson quotients. The same measured amplitudes may be kept through the three independently placed fields before taking either regulator limit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicGalop
open Function Set Filter Finset Metric MeasureTheory Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonMaxwellThermometerFirstDetector WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open XSpace.Tornado XSpace.AxesTangent XSpace.Retirement WilsonMaxwellThermometerInteracting
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) (W : Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)
variable (simple : G.Simple) (B : ℕ)
local notation "k" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "μ" => (fun (r : ℝ) (per : ℕ) =>
  chart R (k r) per (spacing R simple B r) (positive R simple B r))


def quotient (x:Sample 3)(p:Tags G 6 3)(e:ℕ)(S:Finset (Fin 3)):ℂ:=
  ∑f∈tally e 3, if ∀i:Fin 3,i∉S→f (some i)=0 then
    PowerSeries.coeff (f none) (numberA W 6 x (pulseU f (deck (V.layout W (grab x) 6)) p) S)
  else 0

def node (x:Sample 3)(p:Tags G 6 3):ℂ:=
  first (quotient W (V:=V) x p 0) (quotient W (V:=V) x p 1)

theorem enrolled (x:Sample 3)(p:Tags G 6 3):
    sampled W (V:=V) x p=node W (V:=V) x p:=by
  rw [sampled,WilsonMaxwellThermometerInteracting.read]
  apply congrArg₂ first <;> funext S <;> apply detail

theorem basis {I:Fin 3→Type} [∀i,Fintype (I i)](x:Sample 3)
    (sectionI:∀i,I i→Sec G 6)(c:∀i,I i→ℂ):
    node W (V:=V) x (fun i=>∑j,c i j • sectionI i j)=
      ∑a:∀i,I i,(∏i,c i (a i))*node W (V:=V) x (fun i=>sectionI i (a i)):=by
  simp_rw [←enrolled]
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [MultilinearMap.map_smul_univ,smul_eq_mul]

def report (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):ℂ:=
  if h:k r≤z.1 then
    ∑o,weight (Rose.test K) (positions (R:=R) r z) o •
      node W (V:=V) (translated (μ r z.2) (Mesh.back (μ r z.2) ((R.family.S.toDepth h z.2).parent ∘ o))) p
  else 0

theorem entire (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):
    WilsonMaxwellThermometerInheritedCells.filed R W K simple B r z p=report R W K simple B r z p:=by
  by_cases h:k r≤z.1
  · simp only [WilsonMaxwellThermometerInheritedCells.filed,report,dif_pos h,_root_.sum_apply,smul_apply,atSites,enrolled]
  · simp only [WilsonMaxwellThermometerInheritedCells.filed,report,dif_neg h,zero_apply]

variable {R} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (J:ℝ→tower S) {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
    (A:ℝ→Group R.family 6)
local notation "A'"=>WilsonPositionCorrectedCap.adjusted F J V A
local notation "v"=>WilsonPositionGradedThermometerGround.tags

theorem original (hB:0<B)(prior:(Y:Filter _)≤f.fuse)
    (book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J):
    Tendsto (fun w:ℝ×(ℕ×ℕ)=> report R W K simple B w.1 w.2 (v (A' w.1)))
      (trail.curry (Y:Filter _)) (𝓝 ((Rose.c_T K:ℝ):ℂ)):=by
  simp_rw [←entire]
  exact WilsonMaxwellThermometerInheritedCells.original W K simple B F J A hB prior book lead

end YM.Integration.WilsonMaxwellThermometerPublicGalop
