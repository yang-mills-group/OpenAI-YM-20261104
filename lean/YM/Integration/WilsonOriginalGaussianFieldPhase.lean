import YM.Integration.WilsonOriginalGaussianMeasuredVacuum
import YM.Integration.WilsonPositionProgramAngularArm

/-! The entire paid vacuum phase in the actual absolute group coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalGaussianFieldPhase
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 PertExtension.Series AllOrder
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker AllOrder.Laplace Primitives.TwoWave.RealSlice
open QuadraticLocal.Faith Stationary WilsonCoeffUV WilsonCoeffUV.Bank
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}

def field (P:PathData G)(p:Clip)(π:Layout G)(T:Finset Age)(v:ℝ×fieldDir G n 1):ℝ:=
  Costume.evaluation P p T π (v.1,(arm G n 1).symm v.2)

theorem smooth {P:PathData G}{p:Clip}{α C β:ℝ}(bounded:P.Bounds p α C β)
    (π:Layout G)(T:Finset Age)(legal:Legal T π):
    ContDiffAt ℝ ω (Costume.evaluation (n:=n) P p T π) 0:=by
  let Q:=QuadraticLocal.Fk.money (f:=n) π T
  let e:ℝ×Link G n →L[ℝ] ℝ×fieldDir G n 1:=
    (ContinuousLinearMap.fst ..).prod ((arm G n 1).toContinuousLinearMap ∘L ContinuousLinearMap.snd ..)
  let f:=mainTerm p P (n:=n) ∘ input G n
  let g:=Precision.loop P (n:=n) ∘ input G n
  have hf:ContDiffAt ℝ ω f 0:=(Pace.intent_point p P bounded n).analytic.contDiffAt
  have hg:ContDiffAt ℝ ω g 0:=(turns_analytic P.loop bounded.width bounded.two).contDiffAt
  have hq:ContDiffAt ℝ ω (Bulk.projected Q ∘ e) 0:=by
    apply ContDiffAt.comp _ _ e.contDiff.contDiffAt
    simpa only [map_zero] using (QuadraticLocal.Fk.level (f:=n) π T legal).smooth
  change ContDiffAt ℝ ω ((fun x:ℝ×Link G n=>f x.2+x.1^2*g x.2)+(Bulk.projected Q ∘ e)) 0
  refine ContDiffAt.add (ContDiffAt.add ?_ (ContDiffAt.mul (contDiffAt_fst.pow _) ?_)) hq
  · exact hf.comp (f:=Prod.snd) (0:ℝ×Link G n) contDiffAt_snd
  · exact hg.comp (f:=Prod.snd) (0:ℝ×Link G n) contDiffAt_snd

theorem linked {P:PathData G}{p:Clip}{α C β:ℝ}(bounded:P.Bounds p α C β)
    (π:Layout G)(T:Finset Age)(legal:Legal T π)(k:ℕ)(A:fieldDir G n 1):
    Assembly.jet (field P p π T) (k+2) (1,A)=
        Pace.grouping 0 π T p P k n ((arm G n 1).symm A):=by
  let L:ℝ×fieldDir G n 1 →L[ℝ] ℝ×Link G n:=(ContinuousLinearMap.fst ..).prod
      ((arm G n 1).symm.toContinuousLinearMap ∘L ContinuousLinearMap.snd ..)
  rw [Costume.genuine P p T π _ legal bounded]
  exact Assembly.jet_continuous_right L ((smooth bounded π T legal).of_le le_top) (1,A)

theorem first (simple:G.Simple){P:PathData G}{p:Clip}{α C β:ℝ}(bounded:P.Bounds p α C β)
    (π:Layout G)(T:Finset Age)(legal:Legal T π)(A:fieldDir G n 1):
    Assembly.jet (field P p π T) 1 (1,A)=0:=by
  let e:ℝ×fieldDir G n 1 →L[ℝ] ℝ×Link G n:=(ContinuousLinearMap.fst ..).prod
      ((arm G n 1).symm.toContinuousLinearMap ∘L ContinuousLinearMap.snd ..)
  let z:=e (1,A)
  rw [show Assembly.jet (field P p π T) 1 (1,A)=Assembly.jet (Costume.evaluation P p T π) 1 z from
    Assembly.jet_continuous_right e ((smooth bounded π T legal).of_le le_top) (1,A)]
  let e':ℝ×Link G n →L[ℝ] ℝ×fieldDir G n 1:=(ContinuousLinearMap.fst ..).prod
      ((arm G n 1).toContinuousLinearMap ∘L ContinuousLinearMap.snd ..)
  let Q:=QuadraticLocal.Fk.money (f:=n) π T
  let f:=mainTerm p P (n:=n) ∘ input G n
  let g:=Precision.loop P (n:=n) ∘ input G n
  have hf:ContDiffAt ℝ ω f 0:=(Pace.intent_point p P bounded n).analytic.contDiffAt
  have hg:ContDiffAt ℝ ω g 0:=(turns_analytic P.loop bounded.width bounded.two).contDiffAt
  have hQ:=QuadraticLocal.Fk.level (f:=n) π T legal
  have hq:ContDiffAt ℝ ω (Bulk.projected Q ∘ e') 0:=by
    apply ContDiffAt.comp _ _ e'.contDiff.contDiffAt
    simpa only [map_zero] using hQ.smooth
  let u(w:ℝ×Link G n):=w.1^0*f w.2
  let v(w:ℝ×Link G n):=w.1^2*g w.2
  have hu:ContDiffAt ℝ ω u 0:=(contDiffAt_fst.pow _).mul (hf.comp (f:=Prod.snd) (0:ℝ×Link G n) contDiffAt_snd)
  have hv:ContDiffAt ℝ ω v 0:=(contDiffAt_fst.pow _).mul (hg.comp (f:=Prod.snd) (0:ℝ×Link G n) contDiffAt_snd)
  have split:Costume.evaluation (n:=n) P p T π=u+v+(Bulk.projected Q ∘ e'):=by
    funext x
    simp only [Pi.add_apply,u,v,pow_zero,one_mul]
    rfl
  rw [split]
  change Radial.jet (u+v+(Bulk.projected Q ∘ e')) 1 z=_
  rw [jet_add (f:=u+v) (g:=Bulk.projected Q ∘ e') (hu.add hv) hq,jet_add (f:=u) (g:=v) hu hv]
  have closed:Radial.jet f 1 z.2=0:=
    congr_fun ((Pace.audited p P bounded simple n).1 1 (by decide) (by decide)) z.2
  have empty:Assembly.jet (Bulk.projected Q ∘ e') 1 z=0:=by
    rw [Assembly.jet_continuous_right e' (hQ.smooth.of_le le_top), Assembly.jet,hQ.vanish 1 (by decide)]
    simp
  rw [show z=(z.1,z.2) by rfl,favor_exp f hf,favor_exp g hg]
  have null:Radial.jet (Bulk.projected Q ∘ e') 1 z=0:=empty
  simpa [closed] using null

end YM.Integration.WilsonOriginalGaussianFieldPhase
end
