import YM.SignedWilsonExpansion.Grid.Pie
import YM.SignedWilsonExpansion.Contrast.Carbon
namespace YM.SignedWilsonExpansion.Overlap.Expert
/-! # Price log-2. Tests can be designed using from analytic formula alone, prior to any assemblies of Wilson programs or evaluation of phase systems. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token Register
open WickFace PhaseTilt Contrast AxialBill PairWave Marque Mirror Carbon
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(N:WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q)
local notation "u" => four N -- parsed
local notation "T"=> H.details.toServed.toPosted.toQuoted.toContract.toMission.born
local notation "LK" => Real.log 2
local notation "Ω" => Chart.priceR G
variable (x:Scale.Stage 3)(f:Test 3)(ϕ:RealTest 3)(ν:ℝ)
-- receipt explicit over Stage no scaling field. corners meet.
include ν H
lemma foiled : ProbeB.receipt (u) 2 x.val = LK • ((Ω x):ℂ):= by
    rw [ ProbeB.contrast_of ]; have hh:= ( AxialBill.agree Y N.scheme N.criterion S h (T).Taylor (T).still (T).base x LK ν ).1; exact hh.trans ( congr_arg (fun p:ℂ=> LK • p) ( Chart.listed Y N.scheme N.criterion S h (T).Taylor (T).still (T).base x ν ) )
lemma corner : ProbeB.criterion (u) 0 x.val=( ( Fintype.card G.ColorIndex*8*Marque.ticket x 0 1 3 3*Marque.ticket x 0 2 3 3*Marque.ticket x 1 2 3 3:ℝ ):ℂ):= by rw [ ProbeB.defined, Contrast.fee0 ( AxialBill.snapshot Y N.scheme N.criterion S h (T).Taylor (T).still (T).base ν x|>.1 ), Marque.bright ]
def fund (G:Gauge)(f:Test 3):ℂ:= Real.log 2 • f.applyTo ( ProbeB.money ( fun z=> (Chart.priceR G z:ℂ) ) )
lemma priced : ProbeB.quote (u) f 2=fund G f:= by rw [fund, ( Carbon.clockE N H ν Carbon.podium f ).2.2.1, show ProbeB.gain Y N.scheme N.criterion ν=(fun z=> (Ω z:ℂ)) from funext fun z=> Chart.listed Y N.scheme N.criterion S h (T).Taylor (T).still (T).base _ ν ]
structure Golden (G:Gauge)(x:Scale.Stage 3)(φ:RealTest 3) : Prop where
    axial : Holds x
    nonnegative z : 0 ≤ φ z
    center : 0 < φ x.val
    measureΦ : ∫ y:Points 3,φ y=1
    tested (z:Scale.Stage 3) (hh:z.val∈tsupport φ): 0 < Chart.priceR G z
lemma appreciated : Golden G x ϕ ↔ ProbeB.Admire (u) x ϕ:= by
    constructor
    · intro H'; refine ⟨ H'.axial,H'.nonnegative,H'.center,H'.measureΦ,fun a ha=>?_⟩; let z:Scale.Stage 3:= ⟨a,ϕ.tsupport_subset ha⟩; change 0<( ProbeB.receipt ( four N ) 2 z.val ).re; rw [ foiled N H z ν,Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re ]; exact mul_pos (Real.log_pos (by norm_num)) ( H'.tested z ha )
    intro H'; refine ⟨ H'.axis,H'.nonnegative,H'.center,H'.amount,fun z hz=>?_⟩; obtain he:= H'.bound z.val hz; rw [ foiled N H z ν, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re ] at he; exact pos_of_mul_pos_right he ( Real.log_pos (by norm_num) ).le -- left? check
lemma chosen (r:ℝ)(hr:0<r)(hz:Holds x) : ∃ z:RealTest 3, Golden G x z∧tsupport z ⊆ Metric.ball x.val r:= by obtain ⟨z,h₁,h₂⟩:= Carbon.excellent N H ν x hz hr; exact ⟨z,( appreciated N H x z ν ).2 h₁,h₂⟩
end
end YM.SignedWilsonExpansion.Overlap.Expert
