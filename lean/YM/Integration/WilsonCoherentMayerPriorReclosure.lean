import YM.Integration.WilsonCoherentMayerPriorMeasuredFiling
import YM.Integration.OriginalMarkedSignedCutoff

/-! The prescribed proper log is re-exponentiated on the outgoing signed residual.
The physical numerator itself pays its multiplicative relative error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorReclosure
open Lattice Wilson RG Source Marker Precision Exterior
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction ActualOriginalQReaders
open MS.Local.Physical Extra.Histories PhysicalWilsonActionConvention
open RG3.Script.Picnic MergeProof MergeProof.Accent
open WilsonCoherentMayerPriorChronicle (reading)
open WilsonMeasuredPathTaylor WilsonCoherentMayerPriorAtom NativePaidPacketColors
open Comparison.Density.RenderM Next.SectorChange.Flat
open private pass_price from YM.Integration.OriginalMarkedSignedCutoff
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V][Fintype V]{Γ:Census V}

def marked (x:Γ.Mode→ℂ):Poly Γ:=Poly.inject (fun s=>if s=Γ.quiet then 0 else x s)

theorem price {w:V→ℝ}(hw:∀v,0<w v)(L T old Y:Poly Γ)(l0:L.part Γ.quiet=0)
    (t0:T.part Γ.quiet=0)(physical:Y=Poly.pass L*old):
    Poly.pass T*old=Poly.pass (T-L)*Y ∧
    Poly.price w (Poly.pass T*old-Y)≤(Real.exp (Poly.price w (T-L))-1)*Poly.price w Y:=by
  have zero:(T-L).part Γ.quiet=0:=by change T.part _-L.part _=0;rw [t0,l0,sub_self]
  have law:Poly.pass T*old=Poly.pass (T-L)*Y:=by
    rw [physical,←mul_assoc,←Extra.Trajectories.pass_add zero l0,sub_add_cancel]
  refine ⟨law,?_⟩
  rw [law]
  calc
    _ = Poly.price w ((Poly.pass (T-L)-1)*Y):=by rw [sub_mul,one_mul]
    _ ≤ _:= (Poly.multiplication hw _ _).trans (mul_le_mul_of_nonneg_right
      (pass_price _ hw zero) (Poly.nonnegative hw _))

variable {G:Gauge}{R:Run G}{J:Request V}{A:NumericSchedule R.family J}
    {d:LocalFormal.Datum R.family Γ}{F:AnalyticInput J A d}{η:ℝ}{I:FullPreparedInputAt F η}

theorem actual (M:FundedRenderedBank.Catalogue J d)(S:FundedRenderedBank.Bank I M)
    (b:TestSpace J.tests)(U:Config G (R.family.side d.level d.period))(c:ℝ)
    (T:Poly Γ)(quiet:T.part Γ.quiet=0){w:V→ℝ}(hw:∀v,0<w v):
    let Y:=c • actualPush R.family d.cutoff d.period d.level (I.input.leaf b).density U
    let old:=c • (S.output.residual.leaf b).density U
    let L:=M.model.read b (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)) U
    Poly.pass T*old=Poly.pass (T-L)*Y ∧
      Poly.price w (Poly.pass T*old-Y)≤(Real.exp (Poly.price w (T-L))-1)*Poly.price w Y:=by
  intro Y old L
  apply price hw L T old Y (M.model.quiet_read ..) quiet
  dsimp only [Y,old,L]
  rw [S.output.density,S.output.full,S.same_model,mul_smul_comm]

end YM.Integration.WilsonCoherentMayerPriorReclosure
