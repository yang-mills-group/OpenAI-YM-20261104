import YM.Integration.WilsonCoherentMayerHearing
import YM.Planned.PRIMARY_INTEGRAL_295.Xacts

/-! The surviving identity component uses centered Gaussian directions.
Every frozen orbit remains available to the other marked and vacuum factors. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerNoise
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision
open ConnectedActivityE6 Shell Coat SliceRows Channel Push SectorMeasure
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G:Gauge} {c f n:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}

private theorem thinned_one (P:PathData G) (a:Clip) (t:ℝ) (d R:ℕ) (i:Twin n):
    Pressure.thinned P a t d R (1:Config G n) i=0:=by
  have short (j:Cell n) : Pressure.shorten P R d (1:Config G n) j=0:=
    Planned.PrimaryIntegral295.Xacts.plotted_zero a P d R (j,true)
  have direct (j:Cell n) : Pressure.shoot a (1:Config G n) j=0:=
    Planned.PrimaryIntegral295.Xacts.plotted_zero a P d R (j,false)
  rcases i with ⟨j,b⟩; cases b <;> simp [Pressure.thinned,short,direct]

theorem origin (T:Tube G S) (h:S.patch.Branches S.kernel G) (s:ℝ) (k:S.Choices) (i:Rod c f):
    request T s k (1:Config G c) i=0:=by
  have hq:S.prediction (1:Config G f) k=1:=funext fun e=>Push.settled S h e k
  unfold request baseStroke entryCost guide
  rw [replica_one,hq]
  cases i <;> simp [Tube.Xf,Planned.PrimaryIntegral295.Xacts.plotted_zero,Tube.Mv,Tube.Mw,
    Tube.vision,thinned_one,Pressure.zip,Tube.Z,G.curvature_unit]

theorem centered {P:Teller G} (fund:P.Funds S T) (X:Coat T F) (V:X.V=1)
    (clear:Assembly.Clear S X.x X.seeds F):X.μ=0:=by
  have hp (s:Signed):pull s 0 X.V=1:=by
    rw [V]; funext e; unfold pull Step.read; split <;> simp
  have unused:X.signal 0=0:=by
    rw [Coat.signal,X.lens_zero,add_zero]
    funext e
    by_cases h:e∈F.trunks
    · simp [Coat.saved,h]
    · have a:= WilsonCoherentMayerClear.eligible X clear (⟨e,h⟩:F.Free)
      simp [Coat.saved,show X.Hot e from a]
  obtain ⟨_,_,bounds,-⟩:=fund.feeds
  have bill:X.priced 0=0:=by
    funext i
    obtain ⟨s,j⟩:=i
    obtain ⟨D,hD⟩:=SliceRows.linear T X.R bounds s j X.V
    simp [Coat.priced,Coat.realPath,hp,origin T (funds_branch fund),unused,←hD]
  have neutral:stand (X.priced 0)=0:=by rw [bill]; rfl
  unfold Coat.μ Coat.driftM Coat.linearBill
  rw [neutral,Matrix.mulVec_zero,Matrix.mulVec_zero,neg_zero]
  rfl

def row (F:Forest S.ratio) (z:Air f G):Directions G f :=
  fun e=>if e∈F.trunks then 0 else erect G (WithLp.ofLp z) e

theorem drawn {P:Teller G} (fund:P.Funds S T) (X:Coat T F) (V:X.V=1)
    (clear:Assembly.Clear S X.x X.seeds F) {β:ℝ} (pos:0<β) (z:Air f G):
    WilsonCoherentMayerField.direction X β z=row F z :=by
  have mean:=centered fund X V clear
  have hg:(Coat.gStep β)≠0:= by unfold Coat.gStep; positivity
  funext e
  by_cases he:e∈F.trunks
  · simp [WilsonCoherentMayerField.direction,row,he]
  · have h:=WilsonCoherentMayerClear.eligible X clear (⟨e,he⟩:F.Free)
    simp [WilsonCoherentMayerField.direction,row,he,show X.Hot e from h,Coat.liftA,mean,
      smul_smul,hg,Coat.atmos]

end YM.Integration.WilsonCoherentMayerNoise
