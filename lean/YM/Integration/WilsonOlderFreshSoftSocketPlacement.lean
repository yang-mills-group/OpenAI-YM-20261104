import YM.Integration.WilsonOlderFreshSoftSocketWard
import YM.Integration.SignedOpeningSourceCurrent

/-! The same finite all-field incidence after the enrolled knob, film and actual displacement have been applied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketPlacement
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open private covariant from YM.Integration.SignedOpeningSourceCurrent
open WilsonOlderFreshSoftSocketWard (mark)
variable {G:Gauge}{I:Type}[DecidableEq I](D:I→ℕ)(i:I)(κ:Knob (D i))(pt:Chamber)(z:Cover)
private def travel (F:Era G ℝ):Era G (Pen D {i}):=
  cn D i (tuftV ((ContinuousLinearMap.id ℝ ℝ).smulRight (claim (D i) κ pt)) F) z

private theorem one {r:ℕ}(A:RG.Atom G r):
    travel D i κ pt z (mark A)=source D i A κ pt r z:=by
  unfold travel WilsonOlderFreshSoftSocketWard.mark source
  have eq:=covariant A (1:ℝ) ((ContinuousLinearMap.id ℝ ℝ).smulRight (claim (D i) κ pt)) r
  rw [eq];simp

private theorem sum {M:Type}[Fintype M](words:M→Era G ℝ)(coef:M→ℝ):
    travel D i κ pt z (∑m,coef m • words m)=∑m,coef m • travel D i κ pt z (words m):=by
  apply Prod.ext
  · funext n e r v
    simp only [travel,cn,shifted,skewV,revolve,tuftV,ply_v,Prod.fst_sum,Prod.smul_fst,
      Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
  · funext e r v
    simp only [travel,cn,shifted,skewV,revolve,tuftV,ply_v,Prod.snd_sum,Prod.smul_snd,
      Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]

theorem original {M N:Type}[Fintype M][Fintype N]{p:M→ℕ}{q:N→ℕ}
    (A:(a:M)→RG.Atom G (p a))(B:(b:N)→RG.Atom G (q b))(c:M→ℝ)(d:N→ℝ)
    (paid:∀a,(A a).Invariant)(book:∀b,(B b).Invariant)
    (fields:∀(n:Side)(U:Config G n),
      (∑a,c a*(A a).unmasked U 0)=∑b,d b*(B b).unmasked U 0):
    (∑a,c a • source D i (A a) κ pt (p a) z)=∑b,d b • source D i (B b) κ pt (q b) z:=by
  have h:=congrArg (travel D i κ pt z) (WilsonOlderFreshSoftSocketWard.original A B c d paid book fields)
  simpa only [sum,one] using h

end YM.Integration.WilsonOlderFreshSoftSocketPlacement
end
