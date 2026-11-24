import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDigitLedger
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(u:G.ColorIndex)(depth:d<D)
variable (digit:∀i,Site (R.family.S.block i))
variable (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

/-- The two entries of this ledger use the genuinely same marked operation
and its unchanged pupil, on the finite torus and the cover. -/
def ledger (N:ℕ):ℕ→ℕ→Letter (R.family.labels.level d)→Scroll D→Era G ℝ
  | 0, _, v, p => WilsonPointChildFoldedField.field d
      ((sectionY (R.family.localSection d) depth) v) (physical p)
  | h+1, j, v, p =>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
    ∑s,WilsonPointChildEra.funded ((T⁻¹) s v)
      ((P.L.val:ℝ)^d • verseI R.family.path.levels R.metals.O j N d
        (shifted (ledger N h (j+1) s (growWord P (digit j) D p)) (lift (digit j))))

theorem honest (simple:G.Simple)(o:Loc G 1)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D):Auth d (ledger R u depth digit N h j v p):=by
  induction h generalizing j v p with
  | zero=>
    have top:=Roof.topC o (R.family.labels.level d) (R.family.localSection d) R.family.params
      (R.makes.sections d) (Next.Foundations.valuation G d) depth
    exact WilsonPointChildFoldedField.original (clef_through (top.officers v) (slotsFits _ v)) _
  | succ h ih=>
    apply Auth.sum
    intro s _
    apply WilsonPointChildEra.checked
    apply Auth.μ
    exact ((ih (j+1) (by omega) _ _).shifted _).verse _ (by omega) simple R.alloy.B.ratio

theorem translated (X:Era G ℝ)(a:Cover): (shifted X a).2=Kemp.work a X.2:=by
  funext t r x
  change X.2 t r (jog (-a) ∘ x)=X.2 t r ((Lotus.tint (-a)) ∘ x)
  apply congrArg (X.2 t r)
  funext i
  exact Prod.ext (add_comm ..) rfl

include tags in
theorem covered (simple:G.Simple)(o:Loc G 1)(price:ℕ → Gear G → ℝ)
    (paid:FundedMarkedCoverRows.prices price R.kit)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    (ledger R u depth digit N h j v p).2=WilsonPointChildDigitReturn.table R u depth digit N h j v p:=by
  induction h generalizing j v p with
  | zero=>rfl
  | succ h ih=>
    let V:=R.family.path.levels
    let P:=WilsonCoeffUV.loose V j
    let x:=growWord P (digit j) D p
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
    let before(s:Letter (R.family.labels.level d)):=ledger R u depth digit N h (j+1) s x
    let upper(s:Letter (R.family.labels.level d)):=shifted (before s) (lift (digit j))
    let fired(s:Letter (R.family.labels.level d)):=verseI V R.metals.O j N d (upper s)
    let row(s:Letter (R.family.labels.level d)):=WilsonPointChildEra.funded ((T⁻¹) s v) ((P.L.val:ℝ)^d • fired s)
    have hz(s:Letter (R.family.labels.level d)):Auth d (upper s):=
      (honest R u depth digit simple o N h (j+1) (by omega) s x).shifted _
    have eqn(s:Letter (R.family.labels.level d)):(upper s).2=Kemp.work (lift (digit j))
        (WilsonPointChildDigitReturn.table R u depth digit N h (j+1) s x):=
      (translated (before s) _).trans (congrArg (Kemp.work (lift (digit j))) (ih (j+1) (by omega) s x))
    change (∑s,row s).2=_
    rw [Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro s _
    funext e r
    change (affix ((T⁻¹) s v) ((P.L.val:ℝ)^d • (fired s).2)) e r=_
    rw [show (fired s).2=_ from WilsonMarkedCoverIndependentStep.original R u tags simple price paid (N:=N) (j:=j) (by omega) d d le_rfl (upper s) (hz s) o,eqn s]
    simp only [affix,Kemp.surf,Finset.sum_apply,Pi.smul_apply]
    rfl
end YM.Integration.WilsonPointChildDigitLedger
