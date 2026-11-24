import YM.SignedWilsonExpansion.ProbeB
import YM.SignedWilsonExpansion.Belle.Wipe
import YM.FVA2.Main
/-! # Carbon ground & prediction through order two. Independent.
    Seam for calling FVA2.Match before actual comparison. Uses MS_Data at log-scale ν,
    ALL spots on temporal axis (x,y,z), spatial numbering (Lean 1,2,0). -/
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.SignedWilsonExpansion.Carbon
open FVA2 Register FVA2.Arrival Scale Scale.Jury MS MS.Menus MS.High MS.Local.Physical MS.Native MS.Land MS.Fleet
open MeasureTheory Function Filter Set XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Asymptotics PowerSeries Maxwell Maxwell.Free
open WickFace ProbeB Contrast
open Belle Belle.Path Belle.Buffet WilsonCoeffUV.Mer.Xa MarqueQ Crops
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}(N:WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q)
local notation "W"=> Measure.start N.scheme N.criterion 4
local notation "K"=> Measure.outlook N.scheme N.criterion 4
local notation "Z"=> N.scheme
local notation "ψ" => N.criterion
local notation "∂" => Real.log 2
abbrev four : Way G 4:=W -- parser localized next lines
abbrev speakE (p:RealTest 3): ℂ:= quote W (Rose.coerce p) 2
variable (ν:ℝ) (x:Scale.Stage 3)(p:RealTest 3)(f:Test 3)(ht:Holds x) (w:ProbeB.Admire (four N) x p)
local notation "Q'"=> H.details.toServed.toPosted.toQuoted.toContract.toMission.born
local notation "p0"=> Rose.coerce p
-- choose points for definite example. Coord ties ok in Stage.
abbrev lot (t:ℝ):E4:= WickFace.timeLine t
abbrev places: Fin 3→E4:= ![lot 1,lot 6, lot 12]
def podium : Scale.Stage 3:=by
   have u (a b:ℝ)(p:a≠b): lot a≠lot b:=by
      intro h; have t:= sub_ne_zero.mpr p; have ht: basis 3≠0:=fun h=>by obtain h':=basis_norm (3:Axis); rw [h,norm_zero] at h'; norm_num at h'
      exact smul_ne_zero t ht ( by rw [ sub_smul ]; exact sub_eq_zero.mpr h )
   refine ⟨ WithLp.toLp 2 places,show Injective places from ?_ ⟩
   intro a b h; fin_cases a <;> fin_cases b
   all_goals first| rfl | exfalso; first| exact u 1 6 (by norm_num) h|exact u 1 6 (by norm_num) h.symm|exact u 1 12 (by norm_num) h|exact u 1 12 (by norm_num) h.symm|exact u 6 12 (by norm_num) h|exact u 6 12 (by norm_num) h.symm
lemma price_of_poses : Holds podium:= by intro i; fin_cases i <;> first|exact ⟨1,rfl⟩|exact ⟨6,rfl⟩|exact ⟨12,rfl⟩
-- explicit calendar.Rose includes inversion schedule.Front
abbrev lamp (m:XSpace.Mesh)(i:ℕ)(f:Test 3):ℂ:= Deposit m (fun x=> coeff i ( testSeat Z ψ x )) f
include H ν
lemma roots (i:ℕ) : Tendsto (fun k:ℕ=> lamp N ( N.run.step k ) i f ) atTop (𝓝 ( raw W f i )):= ( standing Y Z ψ S h (Q').Taylor (Q').still (Q').base f ν i ).comp H.onSchedule
lemma lampContrast (i:ℕ): Tendsto ( fun m=> lamp N m i f - ( 2:ℂ )^12 * lamp N m i ( ProbeB.double f ) ) Front (𝓝 ( ProbeB.quote W f i )):= ProbeB.removal Y Z ψ S h (Q').Taylor (Q').still (Q').base f ν i
lemma clockE : quote W f 0=0 ∧ quote W f 1=0 ∧ quote W f 2=( Real.log 2 ) • f.applyTo ( ProbeB.money ( gain Y Z ψ ν ) ) ∧ receipt K 2 x.val=receipt W 2 x.val:=by
     refine ⟨ blackout Y Z ψ S h (Q').Taylor (Q').still (Q').base f ν 0 (by decide), blackout Y Z ψ S h (Q').Taylor (Q').still (Q').base f ν 1 (by decide), revenue Y Z ψ S h (Q').Taylor (Q').still (Q').base f ν,?_⟩
     rw [ contrast_of,contrast_of ]; have hx:= AxialBill.agree Y Z ψ S h (Q').Taylor (Q').still (Q').base x (Real.log 2) ν; exact hx.2.trans hx.1.symm
lemma plank : Admire (four N) x p → star ( speakE N p )= speakE N p ∧ 0 < ( speakE N p ).re:=fun t=> ⟨ billed_real Y Z ψ S h (Q').Taylor (Q').still (Q').base p ν, price_pos Y Z ψ S h (Q').Taylor (Q').still (Q').base p ν x t⟩
include ht
lemma axisP : criterion W 0 x.val=( ( (8*Fintype.card G.ColorIndex*pay x 0 1*pay x 0 2*pay x 1 2):ℝ):ℂ ) ∧ receipt W 2 x.val=( Real.log 2*G.casimir/(16*Real.pi^2) ) • criterion W 0 x.val :=⟨order0 Y Z ψ S h (Q').Taylor (Q').still (Q').base ν x ht, at_test Y Z ψ S h (Q').Taylor (Q').still (Q').base ν x ht ⟩
lemma excellent {r:ℝ}(p:0<r): ∃ z:RealTest 3, Admire (four N) x z ∧ tsupport z ⊆ Metric.ball x.val r:= narrows Y Z ψ S h (Q').Taylor (Q').still (Q').base ν x ht r p
end YM.SignedWilsonExpansion.Carbon
