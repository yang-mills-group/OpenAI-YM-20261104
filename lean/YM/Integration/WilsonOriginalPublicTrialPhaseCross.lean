import YM.Integration.WilsonOriginalPublicTrialPhaseTrace
import YM.Integration.WilsonOriginalPublicReflectedGrid

/-! The signed linear detector is paired with the difference of two complete
fitted group words at K, on the original Wilson history with upper date N. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCross
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Cells Push Extra.Histories
open PhysicalNext.Repeat.Legato OPE.Therm OPE.Therm.ReplicaChessboard Push.GridApprox OPE.Strobe
open WilsonOriginalPublicTrialPhaseTrace WilsonOriginalPublicReflectedGrid WilsonPositionProgramBlockedTrialAddBack
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {K N p u:ℕ}
local notation "C" => R.family
local notation "H" => (C).path
local notation "X" i:max => Config G ((C).side i p)
variable {I:Type} [Fintype I]

def diff {B:Type*} (M:Bool → B→ℂ) (U:B):ℂ:=M true U-M false U
def joint (σ:Signed)(seam:Site ((C).side K p))(P Q:X K→ℂ)(U:X K):ℂ:=P U*star (Q (pull σ seam U))
def both (f:Bool→Bool→ℂ):ℂ:=f true true-f true false-f false true+f false false

theorem difference (live:K≤N)(σ:Signed)(seam:Site ((C).side K p))(M:Bool→X K→ℂ)(paid:∀b,Envelope (M b)) :
    pairing R K N p σ seam (diff M) (diff M) = both (fun i j=>pairing R K N p σ seam (M i) (M j)):=by
  let s:=fun b:Bool=>if b then (1:ℂ) else -1
  have h:=matrix R live σ seam s M paid
  have eq:wave s M=diff M:=by funext U;simp [wave,s,diff,sub_eq_add_neg]
  rw [eq] at h
  rw [h]
  unfold both
  simp [s]
  ring

theorem original (live:K≤N)(cut:Cut ((C).side N p))(seam x y:Site ((C).side K p))
    (matchCut:anchor (C).S p live seam=cut.slide)(r:ℕ)(d:I→ℕ)(site:Bool→I→Site ((C).side K p))
    (v:∀(_b:Bool) i,(C).label (d i))(h:ℕ)(probe:(C).label h)
    (fit:∀b i,window (site b i) (stencilRadius (C) (d i))⊆window x r)
    (probeFits:window y (stencilRadius (C) h)⊆window y r)
    (half:∀b:Bool,window (anchor (C).S p live (cond b x y)) (grows (H).levels K r live)⊆cut.sector)
    (far:∀a b:Bool,2*muzzle (H).levels K r<separation (cond a x y) (affine cut.flip seam (cond b x y)))
    (early:u≤K)(salary:ℝ)
    (probeSelf:‖pairing R K N p cut.flip seam (uncut R h N p K y probe) (uncut R h N p K y probe)‖≤ salary):
    let M:=fun b=>word R (N:=N) d (site b) (v b)
    let P:=uncut R h N p K y probe
    let jointM:=fun a b=>joint R cut.flip seam (M a) (M b)
    let E:=fun a b=>actualTransport (C) (N:=N) (jointM a b) early 1
    ∀(entry:Bool→Bool→ℝ),
      (∀a b,‖(∫U,jointM a b U ∂scene (H) N p K)-E a b‖≤entry a b) →
      ‖pairing R K N p cut.flip seam (diff M) P‖^2 ≤
        (‖both E‖+∑a,∑b,entry a b)*salary:=by
  intro M P jointM E entry fee
  have interior(b:Bool):Interior (window x r) (M b):=by
    apply Interior.combines
    exact fun i _=>(WilsonOriginalPublicReflectedTrace.local_trial R (N:=N) (d i) (v b i) (site b i)).enlarges (fit b i)
  let D:=diff M
  have diffPaid:Interior (window x r) D:=by
    have h₀:=(interior true).plus ((interior false).scale (-1))
    change Interior (window x r) (fun U=> M true U-M false U)
    simpa [sub_eq_add_neg] using h₀
  have probePaid:Interior (window y r) P:=(WilsonOriginalPublicReflectedTrace.local_trial R (N:=N) h probe y).enlarges probeFits
  let B:=fun b:Bool=>cond b D P
  have sites(b:Bool):Interior (window (cond b x y) r) (B b):=by cases b <;> first | exact diffPaid | exact probePaid
  let T:=fun b=>backTo (H) N p live (B b)
  have funded(b:Bool):Interior cut.sector (T b):=
    (OPE.Strobe.locale (A:=(H)) (N:=N) (p:=p) (cond b x y) r (sites b) live).enlarges (half b)
  have read(a b:Bool):pairing R K N p cut.flip seam (B a) (B b)=Cells.form ((C).beta N p) cut (T a) (T b):=
    WilsonOriginalPublicReflectedTrace.original R live cut seam _ _ matchCut r (sites a) (sites b) (far a b)
  have β:=Overlay.beta_positive R.makes.wilson (m:=N) (N:=N) (p:=p) le_rfl
  have cross:=Cells.cauchy (Slice.reflected_positive cut ((C).beta N p) β.le) (funded true) (funded false)
  rw [←read true false,←read true true,←read false false] at cross
  have expense:‖pairing R K N p cut.flip seam D D‖≤‖both E‖+∑a,∑b,entry a b:=by
    let L:=fun a b=>pairing R K N p cut.flip seam (M a) (M b)
    have realBill a b : ‖L a b-E a b‖≤entry a b := fee a b
    have identity:both L=both E+((L true true-E true true)-(L true false-E true false)-
        (L false true-E false true)+(L false false-E false false)):=by unfold both;ring
    rw [difference R live cut.flip seam M (fun b=>cylinder_env (interior b))]
    change ‖both L‖≤_
    rw [identity]
    apply (norm_add_le ..).trans
    refine add_le_add le_rfl ?_
    simp only [Fintype.sum_bool]
    calc
      _≤((‖L true true-E true true‖+‖L true false-E true false‖)+‖L false true-E false true‖)+
        ‖L false false-E false false‖:=by grw [norm_add_le,norm_sub_le,norm_sub_le]
      _≤_:=by linarith [realBill true true,realBill true false,realBill false true,realBill false false]
  exact cross.trans (mul_le_mul expense probeSelf (norm_nonneg _) ((norm_nonneg _).trans expense))
end YM.Integration.WilsonOriginalPublicTrialPhaseCross
