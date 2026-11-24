import YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
import YM.Integration.WilsonConditionalTaylorWheelRawVacuum

/-! Put the rented finite upper vacuum on the physical period and the
same independently prescribed canonical forest. The parent, ratio, old
row and both side lengths are transported together. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelPhysicalSide
open AnalyticNext.QuarticMatch.Sheets
open Function Filter Matrix Lattice RG Wilson Precision Tree Bloch Exterior FreeResolvent
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical Matrix
variable {G:Gauge}

theorem transport {n f:Side} (S:StepData n f) (P:Patch) (K:KernelChoices)
    (hp:S.patch=P) (hk:S.kernel=K) (u:PoleRows S.patch) (v:PoleRows P) (row:HEq u v)
    (H Y:FaceRow) (O:ChartRatio G) (U:Crude G):
    winter S (repeatF S) H Y (installed S.ratio u) O (U f)=
      winter (stepAt P K n) (repeatF (stepAt P K n)) H Y
        (installed (stepAt P K n).ratio v) O (U (n*P.L)):=by
  rcases S with ⟨p,k,hs⟩
  change p=P at hp
  change k=K at hk
  subst p;subst k
  replace hs:f=n*P.L:=Subtype.ext hs
  subst f
  replace row:u=v:=eq_of_heq row
  subst u;rfl

theorem forest {n f:Side} (S:StepData n f) (P:Patch) (K:KernelChoices)
    (hp:S.patch=P) (hk:S.kernel=K):
    HEq (repeatF S) (Flat.Lodge.forest (S:=primary P K n) (Flat.routes P)):=by
  rcases S with ⟨p,k,hs⟩
  change p=P at hp
  change k=K at hk
  subst p;subst k
  replace hs:f=n*P.L:=Subtype.ext hs
  subst f
  exact heq_of_eq (WilsonConditionalTaylorWheelCanonicalForest.original (primary P K n))

variable (R:Run G) (N j per:ℕ)
theorem original :
    let A:=R.family.path.levels
    let S:=A.clock.op j per
    let H:=freeForms A N (j+1)
    let Y:=freeForms A N j
    let row:=predictionA A N j
    let n:=R.family.side j per
    let f:=R.family.side (j+1) per
    Winding.coil0 A R.metals.O j N n =
      winter S (repeatF S) H Y (installed S.ratio row) R.metals.O
        (Winding.emera (actionW A R.metals.O N (j+1)) f):=by
  intro A S H Y row n f
  exact (transport S (loose A j) A.clock.kernel rfl rfl row row HEq.rfl H Y R.metals.O _).symm

end YM.Integration.WilsonConditionalTaylorWheelPhysicalSide
end

