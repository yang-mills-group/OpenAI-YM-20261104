import YM.Integration.WilsonCoherentInheritedSpool

/-! The original before-period spool permit evaluated at every inherited
physical temperature. Its fields are the original issued oven, directions,
stage, constants and numerical roster checks on every finite side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentInheritedPermit
open Filter Real Lattice Wilson RG Tree Precision
open RGComparison.Core16 RGComparison.Core16.Lumen PertExtension.Series.Tested FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (J:I→Spool.Lamp G) (cap:ℝ) (r:ℕ) (start:Lumen.Stage)

def offered (i:ℕ):Prop :=
  let H:=WilsonCoherentFiniteIssue.stagePatch R i
  let K:=R.family.path.levels.clock.kernel
  let x:=R.family.path.levels.clock.hatBeta i
  ∃(P:Parcel.Oven H) (X:P.Form G) (U:Lumen.Stage) (C:ℝ),
    P.Offers X K ∧ X.Q=cap ∧ U.Above start ∧ 0≤C ∧ C≤2+log x ∧
    (sqrt (x/2))⁻¹≤Forge.dollar U.L ∧ ∀(c f:Side)(size:f.val=c.val*H.L.val),
       let S:StepData c f:=⟨H,K,size⟩
       Bid.Larger (G:=G) S→∀(T:Forest S.ratio)(u:Pins G c)(o:I→Site f),(∀a,‖u a‖≤cap)→
       Spool.Price U r C (Spool.rank J S T X (Next.Foundations.chart G) u o) (Spool.reads J S u o)

theorem purchased (simple:G.Simple) (big:∀i per,Bid.Larger (G:=G) (R.family.path.levels.clock.op i per))
    (credit:∀ᶠ i:ℕ in atTop,offered R J cap r start i) :
    ∀ᶠ i:ℕ in atTop,∀N per:ℕ,i+1≤N→let a:=R.family.path.levels
      let S:=a.clock.op i per
      let g:=regulatorRun R.family N per (i+1)
      ∀(T:Forest S.ratio)(u:Pins G (R.family.side i per))(o:I→Site (R.family.side (i+1) per))
        (tag:S.Choices)(v:(Descent.nil (top:=R.family.side (i+1) per)).Tags),
      (∀k,‖u k‖≤cap)→
      ‖Spool.reads J S u o g-peval (WilsonCoherentJointReturn.series J S T R.metals.O u o (big i per) tag v) r g‖
        ≤g^(r+1)*(2+log (a.clock.hatBeta i)):=by
  filter_upwards [credit] with i issued N per live a S g T u o tag v inside
  obtain ⟨P,X,U,C,offer,width,_,_,expense,aperture,receipt⟩:=issued
  exact WilsonCoherentInheritedSpool.measured R simple i N per live J X aperture expense offer (big i per)
    T u o (fun k=>(inside k).trans_eq width.symm) (receipt _ _ S.sizes (big i per) T u o inside) tag v

end YM.Integration.WilsonCoherentInheritedPermit
