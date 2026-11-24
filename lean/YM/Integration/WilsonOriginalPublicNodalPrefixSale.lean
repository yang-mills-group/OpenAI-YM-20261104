import YM.Integration.WilsonOriginalPublicNodalPrefixVote

/-! Measured finite Taylor income on a common grouped initial interval, allowing different cutoffs and clocks. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefixSale
open Lattice RG Source Labels PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo
open RegulatorIR.Oracle RegulatorIR.Older RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Calibration RegulatorIR.Uniform RegulatorIR.Clocks RegulatorIR.FVAAlt2
open WilsonIndependentRawRosterOrbit (report)
open WilsonOriginalPublicNodalPrefixFree (Route)
open WilsonOriginalPublicNodalPrefixCut (height last into cut clock own line)
open scoped Classical
variable {G:Gauge}{I X X':Type}{M:X → ℕ}{M':X' → ℕ}{n:Page M → Side}{n':Page M' → Side}
    (C:Circuit M n)(D:Circuit M' n')(j:Choice M)(k:Choice M')(x:X)(y:X')(T:Route C D j k x y)
    (birth:C.l (Page.opening _ x)=D.l (Page.opening _ y))
    {K:KernelChoices}(Y:Program K)(Z:∀P:Patch,P.Branches K G)(col:G.ColorIndex)
    (F:Tent M)(F':Tent M'){p:ℕ}
    (one:Notebook C Y G Z col (Rocket.native _) F p)(two:Notebook D Y G Z col (Rocket.native _) F' p)
    (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)(sites:X → I → Cover)(homes:X' → I → Cover)

include T birth one two in
theorem original (same:sites x=homes y)(t:ℕ)(a:t≤j.age x)(b:t≤k.age y):
    Matches p ((report R W σ d key arms (C.payroll Y G Z (sheet F)) sites).main (briefly j x t a))
      ((report R W σ d key arms (D.payroll Y G Z (sheet F')) homes).main (briefly k y t b)):=by
  let S:=cut C j x
  let J:=last (j.age x)
  let Xc:=clock j x (le_refl (j.age x)) F
  let Yc:=clock k y T.age.le F'
  let pos:Unit → I → Cover:=fun _=>sites x
  have first:=WilsonOriginalPublicNodalPrefixCut.notebook C C j j x x (own C j x) rfl Y G Z col F one
  have second:=WilsonOriginalPublicNodalPrefixCut.notebook C D j k x y T birth Y G Z col F' two
  have lhs:=WilsonOriginalPublicNodalPrefixFrame.active S C J j () x (line C C j j x x (own C j x))
    rfl Y G Z Xc F (fun _ _ _=>rfl) R W σ d key arms pos sites rfl t a a
  have rhs:=WilsonOriginalPublicNodalPrefixFrame.active S D J k () y (line C D j k x y T)
    birth Y G Z Yc F' (fun _ _ _=>rfl) R W σ d key arms pos homes same t a b
  rw [←lhs,←rhs]
  exact WilsonOriginalPublicNodalPrefixVote.measured S Y Z col Xc Yc first second R W σ d key arms pos _

include T birth one two in
theorem scalar (same:sites x=homes y)(q:ℕ)(hp:q≤p):
    note ((report R W σ d key arms (C.payroll Y G Z (sheet F)) sites).main (j.choose x) q 0)=
      note ((report R W σ d key arms (D.payroll Y G Z (sheet F')) homes).main (k.choose y) q 0):=by
  have h:=original C D j k x y T birth Y Z col F F' one two R W σ d key arms sites homes same
    (j.age x) le_rfl T.age.le q hp
  have atRight:briefly k y (j.age x) T.age.le=k.choose y:=by
    change (⟨y,j.age x,_⟩:Page M')=⟨y,k.age y,_⟩
    congr 1
    exact T.age
  rw [atRight] at h
  exact congrArg (fun A=>note (A 0)) h

end YM.Integration.WilsonOriginalPublicNodalPrefixSale
end
