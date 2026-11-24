import YM.Integration.WilsonPhysicalNodalPrimitiveEntrance
import YM.Integration.WilsonMeasuredPublicEntrancePinnedPass

/-! A turned physical source on the original acquired axes. The group action
acts on the fitted K coefficient before its engineering restoration and
appears in the same place in the finite inversion figure. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalOrientedStencilPin
open Function Filter Finset Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open XSpace XSpace.Cirrus PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2 Extra.Histories
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalIndependent (forecast)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonMeasuredPublicEntranceCellWords (physical submitted difference)
open WilsonMeasuredPublicEntrancePinnedPass (ear)
open WilsonPositionProgramReportedField (entire)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(W:Initialize G){n N per K f u:ℕ}(d:Fin n→ℕ)
  (file:Filed R d K)(fk:f≤K)(kn:K≤N)(uk:u≤K)
  (Y:∀a,R.family.label (d a))(turn:Fin n→Motion)
  (loc:Fin n→Site (R.family.side f per))(node:Sample n)
  {h:Fin n→ℕ}(κ:(a:Fin n)→Knob (h a))(pt:Fin n→Chamber)(s:(Stock.census (Fin n)).Mode)

def dosesAt (i:Fin n):R.family.label (d i):=
  units R d K (fun a=>Motion.patch (R.family.labels.level (d a)) (turn a)
    (doses R d file.station (N:=N) (per:=per) (file.A N per) Y a)) i

def coordinates (i:Fin n):R.family.label (d i):=
  entire R (d i) K (N,per) (dosesAt R d (N:=N) (per:=per) file Y turn i)

local notation "w" => dosesAt R d (N:=N) (per:=per) file Y turn
local notation "g" => regulatorRun R.family N per K
local notation "seen" => actualTransport R.family (N:=N) (p:=per)
local notation "pins" => (fun i=>wrap (R.family.side K per) (node.layout i))
local notation "α" b:max => weight R d N per K (w) s.val b
local notation "raw" => physical R d (N:=N) Y turn loc s
local notation "figure" Q:max => evaluated Q g (board R W d (coordinates R d (N:=N) (per:=per) file Y turn) node s.val)
local notation "paid" Q:max b:max => forecast R d κ pt s.val node.layout node.F.p (W.tree node.F.p) Q g b
local notation "earK" b:max => seen (word R d κ pt g pins s.val b) uk 1
local notation "gap" => WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) raw
local notation "row" Q:max => (∑b:Selection R d s.val,α b*(earK b-paid Q b))
local notation "located" => (∀i∈s.val,pins i=(R.family.S.toDepth fk per).embed (loc i))

theorem original (placed:located)(Q:ℕ):
    R.family.omega N per raw-gap-figure Q-row Q=
      difference R d file fk kn uk Y turn loc s:=by
  have fit:figure Q=∑b:Selection R d s.val,α b*paid Q b:=
    WilsonOriginalPublicNodalIndependent.valued R d κ pt (p:=per) kn (w) s.val
      node.layout node.F.p (W.tree node.F.p) Q g
  have intake:submitted R d (N:=N) file fk Y turn loc s=
      fun U=>∏a:s.val,WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K
        (pins a) ((w) a) U:=by
    funext U
    let cut (i:Fin n)(o:Site (R.family.side K per)):=WilsonPositionProgramBlockedTrialAddBack.uncut R
      (d i) N per K o ((w) i) U
    change (∏i∈s.val,cut i ((R.family.S.toDepth fk per).embed (loc i)))=
      ∏a:s.val,cut (a:Fin n) (pins a)
    calc
      _=∏i∈s.val,cut i (pins i):=by
        apply prod_congr rfl
        intro i hi
        rw [placed i hi]
      _=_:=(Finset.prod_coe_sort s.val (fun i=>cut i (pins i))).symm
  have actual:ear R d file fk kn uk Y turn loc s=∑b:Selection R d s.val,α b*earK b:=by
    unfold ear WilsonThermometerUnitFilingFlatTelescope.numerator
    rw [WilsonThermometerUnitFilingPosterior.weighted R (N:=N) (p:=per) _ uk,intake]
    exact WilsonReceivedCanonicalVersePosterior.original R d κ pt N per K kn (w) pins s.val u uk 1
  have original:=WilsonMeasuredPublicEntrancePinnedPass.phase R d file fk kn uk Y turn loc s
  dsimp only at original
  rw [actual] at original
  rw [fit]
  simp only [mul_sub,sum_sub_distrib]
  linear_combination original

theorem commissioned {requested power t:ℕ}{B:ℝ}
    (A:Panel R d N per f K fk kn requested power t B)(station:A.slot=file.station)
    (axes:A.axis=file.A N per)(held:u≤f)(sale:Reading R d A held)(one:∀v,1≤A.M v)
    (E:Fin n→ℕ)(refs:∀v b,b≤d v→R.family.ref b≤N)
    (fare:∀v,Next.Rank.Spindle.paid R.family (d v) f N per (A.names v)≤
       A.M v*(R.family.path.levels.clock.hatBeta f)^(E v))
    (desired:ℕ)(exposure:desired+∑v∈s.val,E v≤requested)
    (spots:∀i∈s.val,pins i=(R.family.S.toDepth fk per).embed (A.loc i))(Q:ℕ):
    let upper:=physical R d (N:=N) A.names A.turn A.loc s
    let correction:=WilsonOriginalTwoFlatGridScaling.gap R N per u (held.trans (fk.trans kn)) upper
    let cash:=dosesAt R d (N:=N) (per:=per) file A.names A.turn
    let table:=board R W d (coordinates R d (N:=N) (per:=per) file A.names A.turn) node s.val
    ‖R.family.omega N per upper-correction-evaluated Q g table-
      ∑b:Selection R d s.val,weight R d N per K cash s.val b*
        (seen (word R d κ pt g pins s.val b) (held.trans fk) 1-paid Q b)‖≤
      (∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d v) (A.M v))*
        ((R.family.path.levels.clock.hatBeta f)^desired)⁻¹:=by
  intro upper correction cash table
  rw [original R W d file fk kn (held.trans fk) A.names A.turn A.loc node κ pt s spots Q]
  exact WilsonMeasuredPublicEntranceCellWords.paid R d A file station axes held sale one E refs fare s desired exposure

end YM.Integration.WilsonPhysicalOrientedStencilPin
end
