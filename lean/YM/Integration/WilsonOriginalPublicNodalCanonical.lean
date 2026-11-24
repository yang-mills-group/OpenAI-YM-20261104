import YM.Integration.WilsonOriginalPublicNodalUnits
import YM.Integration.WilsonReceivedCanonicalVersePosterior
import YM.Integration.WilsonPositionProgramBlockedTrialFiling

/-! Actual unsuspended public figures as paid canonical Wilson socket requests. -/
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonOriginalPublicNodalCanonical
open Finset Lattice Wilson RG RG16.Literal Labels Source Next.Rank Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark
open WilsonThermometerPositionTunedSlope (Columns)
open PhysicalNext.Repeat.Legato Extra.Histories
open WilsonOriginalPublicNodalTransport (group)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonPositionProgramReportedField (entire)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)(z:I→ Cover)
    (a:Columns R d){N p K u:ℕ}
local notation "F" i:max => R.family.labels.level (d i)
local notation "g" => regulatorRun R.family N p K
local notation "τ" => (R.family.path.rep N p K).p.threshold
local notation "X" j:max => Config G (R.family.side j p)
local notation "point" => fun i=>wrap (R.family.side K p) (z i)

/-- The real, thermal threshold pays the unsuspended public basis. -/
def request (i:I):(F i).Coeff:= (F i).scaled τ (Pi.single (a i) 1)

omit [Fintype I] [LinearOrder I] in
theorem ray (i:I):entire R (d i) K (N,p) (request R d a (N:=N) (p:=p) (K:=K) i)=
    (F i).scaled g (Pi.single (a i) 1):=by
  have ht:τ≠0:=(R.family.path.rep N p K).p.threshold_pos.ne'
  funext b
  simp only [request,entire,gMap,Frame.scaled_apply,←mul_assoc,←Complex.ofReal_mul,←mul_pow,
    div_mul_cancel₀ _ ht]

local notation "v" => request R d a (N:=N) (p:=p) (K:=K)

omit [Fintype I] [LinearOrder I] in
theorem fee (i:I):(F i).coeffSize (v i)=τ^((F i).grades (a i)).2:=by
  unfold Frame.coeffSize
  rw [sum_eq_single (a i)]
  · simp [request,Frame.scaled_apply,abs_of_pos (R.family.path.rep N p K).p.threshold_pos]
  · intro b _ h; simp [request,Frame.scaled_apply,Pi.single_eq_of_ne h]
  · simp

omit [Fintype I] [LinearOrder I] in
theorem letter (kn:K≤N)(i:I)(U:X K):
    uncut R (d i) N p K (point i) (v i) U=
      (R.family.localSection (d i)).places (Pi.single (a i) 1) (point i) U:=by
  have gp:g≠0:=(ActualRunKernelPackets.regulator_pos R N p K kn).ne'
  rw [WilsonPositionProgramBlockedTrialFiling.filed R (d i) N p K kn,ray,sum_eq_single (a i)]
  · simp only [Frame.scaled_apply,Pi.single_eq_same,mul_one,WilsonPositionProgramBlockedTrialFiling.atomAt,
      Complex.real_smul,Complex.ofReal_inv,←mul_assoc,Complex.ofReal_pow]
    rw [mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr gp)),one_mul]
  · intro b _ h; simp [Frame.scaled_apply,Pi.single_eq_of_ne h]
  · simp

variable {h:I→ℕ}(κ:(i:I)→Knob (h i))(pt:I→Chamber)(S:Finset I)
local notation "fig" => group R (fun i:S=>d i) (fun i:S=>z i) (fun i:S=>a i) (R.family.side K p)
local notation "row" => word R d κ pt g point S
local notation "cash" => weight R d N p K v S
local notation "T" => actualTransport R.family (N:=N) (p:=p)

theorem opened (kn:K≤N)(before:u≤K)(U:X u):
    T fig before U=∑q:Selection R d S,cash q*T (row q) before U:=by
  have physical:(fun V:X K=>∏i:S,uncut R (d i) N p K (point i) (v i) V)=fig:=by
    funext V
    rw [WilsonOriginalPublicNodalUnits.product]
    exact prod_congr rfl fun i _=>letter R d z a kn i V
  rw [←physical]
  exact WilsonReceivedCanonicalVersePosterior.original R d κ pt N p K kn v point S u before U

theorem paid (kn:K≤N)(before:u≤K)(U:X u)(wick:Selection R d S→ℂ){ε:ℝ}(ep:0≤ε)
    (sockets:∀q:Selection R d S,‖T (row q) before U-wick q‖≤ε):
    ‖T fig before U-∑q:Selection R d S,cash q*wick q‖≤
      wallet R d (fun i=>τ^((F i).grades (a i)).2) S*ε:=by
  rw [opened R d z a κ pt S kn before U]
  exact WilsonReceivedCanonicalVersePortfolio.signed R d N p K kn v S _ (fun i _=>(fee R d a i).le)
    (fun q=>T (row q) before U) wick ep sockets

end YM.Integration.WilsonOriginalPublicNodalCanonical
end
