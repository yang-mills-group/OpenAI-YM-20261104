import YM.Integration.WilsonIndependentPublicCoverFields
import YM.WilsonCoeffUV.Product.I.Cruise

/-! The actual older marked recurrence using the public conditional lines and unchanged incoming action. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonIndependentPublicCoverCruise
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open Embroider Embroider.Canvas
variable {G:Gauge}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}
variable {V:Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem index {X Y α β:Type}{F F':Side→Type}(U:Quarry X α F)(W:Quarry Y β F')(v:Row α β):
    cargo U W (lading U W v)=v:=by
  funext a b z
  simp [cargo,lade_eq,Quarry.cabin,Quarry.boom]

private theorem finite (A:Levels G)(Ñ:ChartRatio G)(N m k:ℕ)(Z:Era G V)(P:Patch)(K:KernelChoices)
    (H:FreeResolvent.FaceRow)(a:PoleRows P)(patch:P=loose A m)(kernel:K=A.clock.kernel)
    (free:H=freeForms A N (m+1))(row:HEq a (predictionA A N m))(c:Side):
    (verseI A Ñ m N k Z).1 c=Blue.mix (ratioHigh A Ñ N m) (reed (avenue P K c) (xree P K c) H
      (installed (tileB P.L c) a) Ñ ((story A Ñ N (m+1)).1 (c*P.L)) k (Z.1 (c*P.L))) :=by
  subst P K H
  have h:a=predictionA A N m:=eq_of_heq row
  subst a
  rfl

variable {A:Levels G}{C:Circuit M n}{K:KernelChoices}{s:ℕ}{w:Ω}
theorem original (bill:WilsonIndependentPublicFreeTrain.Matches A C K s w)
    (Y:Program K)(branches:∀ P:Patch,P.Branches K G)(f:Flap M)(hf:f.volW=w)
    (Ñ:ChartRatio G)(Z:Era G V)(k start:ℕ)(fresh:s+(M w-(f.offset+1))<start):
    let N:=s+M w
    let m:=s+(M w-(f.offset+1))
    let B:=blockQ G (loose A m).L
    let P:=C.pactP f
    let incoming:=cruises A Ñ N k start (m+1) Z
    let reset:=ratioHigh A Ñ N m
    let before:=story A Ñ N (m+1)
    (∀ c:Side,(cruises A Ñ N k start m Z).1 c=
      Blue.mix reset (reed (avenue P K c) (xree P K c) (C.tables Y f.prev).diagonal
        (installed (tileB P.L c) (C.tells Y f)) Ñ (before.1 (c*P.L)) k (incoming.1 (c*P.L)))) ∧
    (cruises A Ñ N k start m Z).2=Blue.mix reset (windsT (loose A m) A.clock.kernel Ñ
      (shuttleM (cargo B B (C.pulses Y G branches f))) (shuttleM (cargo B (linksQ G) (C.sails Y G f)))
      before.2 k incoming.2) :=by
  intro N m B P incoming reset before
  rw [cruises_sub A Ñ N k Z fresh]
  have good:f.offset<M w:=hf ▸ f.ok
  have prior:m+1=s+(M w-f.offset):=by dsimp [m];omega
  have table : (C.tables Y f.prev).diagonal=freeForms A N (m+1):=by
    rw [prior]
    exact WilsonIndependentPublicFreeTrain.diagonal bill Y f.prev hf
  obtain ⟨heat,mean⟩:=WilsonIndependentPublicCoverFields.original bill Y branches f hf
  refine ⟨finite A Ñ N m k incoming P K _ _ (bill.patches f hf).symm bill.kinetic.symm table
    (WilsonIndependentPublicFreeTrain.predictor bill Y f hf).symm,?_⟩
  rw [heat,mean,index,index]
  rfl

end YM.Integration.WilsonIndependentPublicCoverCruise
