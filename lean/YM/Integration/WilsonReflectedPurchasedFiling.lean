import YM.Integration.WilsonReflectedCaptureWallet
import YM.Integration.WilsonReflectedTerminalWallet
import YM.Integration.WilsonReflectedFiledOutput

/-! The original reflected funding theorem with both numerical purchases made
before the cutoff, period, and independent positions are submitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedPurchasedFiling
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Next.Rank Ribbon Trace.Physical
open WilsonThermometerOwnOffsetRadii WilsonReflectedMicroscopicSites
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Set Filter OPE Next.UVStress
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {I:Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {A:Type*} {l:Filter A} {T:A→ℝ} {m k:A→ℕ}
set_option quotPrecheck false
local notation "C" => R.family
local notation "B" => R.family.path.levels.budget
local notation "φ" => near R.alloy.B.a
local notation "X" => bling R.alloy.B.a

include simple book in
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (D h u J:ℕ)
    (active:R.family.ref h ≤ u) (time:Tendsto T l atTop)
    (cap:Height R.family.S l T m 1) (fine:Height R.family.S l T k 1) :
    ∃ Z:A→ℝ, RateIs l T Z 0 ∧
      RateIs l T (fun j=>terminalCost R.family h (m j) (Z j)) (-(h:ℝ)) ∧
      ∀ᶠ j in l,∀(N p:ℕ) (kn:k j<N) (mk:m j+1≤k j) (ub:u ≤ m j)
        (opened:Opened R.family h u p) (tiling:Stock.Tabs.opens R.family.path.levels 1 J u)
        (_ : GridApprox.room R.family.path.levels J (m j) (lensScope R.family h))
        (i₀:I) (d:I→ℕ) (_ : ∀i,d i≤D) (z:I→Site (R.family.side N p))
        (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i))
        (_ : ∀i,WilsonThermometerOffsetTrajectory.Enrolled R.makes R.doors
          (WilsonThermometerOffsetLedger.cash R) (k j) N p (d i)
          (WilsonThermometerOffsetResidue.digits R N p (z i)) (V i) (r i))
        (y:(i:I)→Palette R.family (d i)) (_ : ∀i,size (y i)≤1)
        (_ : WilsonThermometerOwnOffsetNectar.location R (z i₀) (m j+1)=0),
        let o:=site (J:=J) R z
        (∀a,m j+1≤a→a≤k j→Cross (B a).B (o a)) →
        (∀a c,a≠c→(B (k j)).B^2 < separation (o (k j) a) (o (k j) c)) →
        (∀i:Site (R.family.side J p)×I,coverNumber (B (m j+1)).B
          ({o (m j+1) (i.1,i₀),o (m j+1) i}:Support _)≤1) →
        let mn:=(m j).le_succ.trans (mk.trans kn.le)
        let tiled:=center R.family.S p (tiling.1.trans (ub.trans mn)) 0
        let f:Cut R.family N p:=fun U=>∏i,WilsonThermometerIntrinsicRoster.source R d z y r kn.le i U
        Interior (tiled.chamber 0) f →
        (∀x:R.family.label h,Interior (tiled.chamber 0) (R.family.O N p x 0)) →
        ∃(q:store R.family h p (m j)) (x:R.family.label h),
          Funds R.family R.makes p N (m j) h J u (terminalCost R.family h (m j) (Z j))
            (R.family.S.a (m j+1)^h*(X (m j)*(4*(1/Z j))))
            (Real.exp (((h:ℝ)+1/16)*T j)) f tiling.1 ub mn opened x q :=by
  obtain ⟨t,_,physical⟩:=WilsonReflectedThermometerCapture.original (I:=I) R simple book shop D
  obtain ⟨α,Z,_,issued,capital,launch⟩:=
    WilsonReflectedCaptureWallet.original R simple book I t h time cap fine
  have roomPrice:=WilsonReflectedTerminalWallet.original R simple book u h active time cap issued capital
  refine ⟨Z,issued,capital,?_⟩
  filter_upwards [fine.grows.eventually physical,roomPrice] with j appointment fees
  dsimp only
  intro N p kn mk ub opened tiling room i₀ d degree z V r money y small anchor cross separated covered intF intBasis
  let f:Cut R.family N p:=fun U=>∏i,WilsonThermometerIntrinsicRoster.source R d z y r kn.le i U
  let w:=Real.exp (((h:ℝ)+1/16)*T j)
  let dR:=R.family.S.a (m j+1)^h*(X (m j)*(4*(1/Z j)))
  have pos:0<w:=Real.exp_pos _
  obtain ⟨pa,one,all,roof,pz,fz⟩:=launch j
  have xPos:0 < X (m j):=(banket R.family simple).pos _
  have scalePos:=R.family.S.a_pos (m j+1)
  have drPos:0<dR:=by dsimp [dR];positivity
  have pay:(∀a:Site (R.family.side J p),0 < march (fun _:Site (R.family.side J p)=>w) φ u (m j) a):=by
    intro a
    generalize m j = b
    induction b with
    | zero=>exact pos
    | succ b ih=>simp only [march];split
                 · exact mul_pos ((mintN R.family simple).2.pos _) ih
                 · exact pos
  obtain ⟨q,whole,reads,sz,_⟩:=appointment p N (m j) J h kn (tiling.1.trans ub) mk (active.trans ub)
    i₀ d degree z V r money y small anchor cross separated (carpet R.family.path (m j)) (α j) (Z j)
    pa one (fun a _ ak=>all a ak.le) (all (m j) ((m j).le_succ.trans mk))
    (fun i=>(covered i).trans roof) pz fz.le _ pay
    (fun i=>(WilsonReflectedTerminalWallet.constant w φ u (m j) i).le.trans fees.1)
  have cont:Continuous f:=continuous_finsetProd _ (fun i _=>
    (R.family.continuousO N p (d i) _ (z i)).const_smul ((R.family.S.a (k j):ℂ)^(d i)))
  obtain ⟨x,paid⟩:=WilsonReflectedFiledOutput.original R simple opened tiling ub
    ((m j).le_succ.trans_lt (mk.trans_lt kn)) room f cont intF intBasis q reads
    (M:=2*dR) (by change _+dR≤2*dR;change _≤dR at sz;linarith) (mul_pos zero_lt_two drPos)
    (E:=terminalCost R.family h (m j) (Z j)) le_rfl pos fees.2 whole
  exact ⟨q,x,paid⟩
end YM.Integration.WilsonReflectedPurchasedFiling
