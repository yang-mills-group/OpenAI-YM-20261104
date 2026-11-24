import YM.SignedWilsonExpansion.Result.Orders
import YM.GradedFar.Compass
import YM.GradedFar.Batch
import YM.GradedFar.Sunlight

noncomputable section
namespace YM.Integration.GradedFar.AppointedDerivativeFrames
open YM YM.Answer.ContinuumLimit YM.Answer.ContinuumLimit.Vision
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics Set Real PowerSeries
open YM.FVA2.GradedFar YM.Integration.GradedFar YM.Integration.GradedFar.Batch
open Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Tariff.Tickets
open FVA2.O.Enh FVA2.Dframe FVA2.Scale.Facets FVA2.Scale.Equator
open YM.FVA2.Scale.Jury SignedWilsonExpansion.Belfry SignedWilsonExpansion.Belfry.ScaleFits SignedWilsonExpansion.Dancer
open scoped ContDiff Topology Classical BigOperators
universe u
open YM.Answer.ContinuumLimit YM.Answer.ContinuumLimit.Vision
variable {G:Gauge}{H:G.Simple}{e:Axis}{ε:ℝ}{O:OrderS G}{E:Construction.{u} H ε e O}{f:Extraction.Order}
variable {Z:WilsonPrescription G}(V:Vision E f)(Q:Perspective H Z true)


local notation "Fv" => V.pupil.last
local notation "P" => V.Post Z
local notation "θ" => V.T Z
local notation "Xv" => Scale.Measure.outlook Z.scheme Z.criterion
private theorem salary {ι:Type} (l:Filter ι) {d:ℕ} (u:Sec G d) :
    SeatsW.Salary ℂ l 1 (fun _ => u) := by
  intro χ
  exact IsBigO.of_bound ‖χ u‖ (Eventually.of_forall fun _ => by simp)

include Q in
theorem clock : Coupling G θ := Fire.from_timer H θ (Appointment.measured V Q)

include Q in
theorem prepared : Prepared Fv (V.Pre Z) P Z θ :=
  YM.Integration.GradedFar.earning Fv V.pupil.J Z Q.MS Q.matching V.pupil.VFrame.2 (clock V Q)

theorem field {n h:ℕ} (v:Peers V) (r:ℝ) (x:Points n) (u:ListInput G n h) :
    Life Z V true r (Ceiling n h) u x v = frank Fv P v h r x u := rfl

theorem forecast {n h:ℕ} (p:ℕ) (t:ℝ) {x:Points n} (clear:x∈conf n) (u:ListInput G n h) :
    Path.mote (Lamplight Z true h) p x t u = appointedH140Crop p t (sent Xv h x u) := by
  rw [Path.pollen (Lamplight Z true h) ⟨x,clear⟩ u t p, YM.SignedWilsonExpansion.Dancer.Drawing.atW, crop_eq]
  apply Finset.sum_congr rfl
  intro k _
  rw [cashed Xv u clear k]
  rfl

include Q in
theorem compact {n h:ℕ} (p:ℕ) (K:Set (Points n)) (hK:IsCompact K) (clear:K⊆conf n)
    (u:ListInput G n h) :
    ∃ C:ℝ, 0 ≤ C ∧ ∀ᶠ r in trail, ∀ v:Peers V, ∀ x:K,
      ‖frank Fv P v h r x.val u-appointedH140Crop p (θ r) (sent Xv h x.val u)‖ ≤ C*|θ r|^(p+1) := by
  have accounts := ((Appointment.pricesAll V).2 Z true Q).estimates
  let own : ∀ j:Fin n, Ceiling n h j ≤ h := fun _ => le_rfl
  obtain ⟨C,hC,hp⟩ := (accounts.trueLetters p trail id tendsto_id K ⟨hK,clear⟩
    (Teller.logNu 1) (Ceiling n h) own (fun _=>u) (fun j=>salary trail (u j))).1 true
  have selfcap : YM.Integration.Election.Frames.toView (Ceiling n h) h own G u = u := by
    funext j
    change Normalize.up (le_rfl : h ≤ h) (u j) = u j
    rfl
  refine ⟨C,hC.le,hp.mono ?_⟩
  intro r hr v x
  have comparison := hr v ⟨x.val,clear x.property⟩ x.property
  simpa only [selfcap,field,forecast p (θ r) (clear x.property) u,id_eq] using comparison

include Q in
theorem classes (n h:ℕ) : ClassExpansion Fv P Xv θ n h := by
  intro K hK clear u
  constructor
  · intro k
    apply FVA2.GradedFar.Cart.Charge.cap
    obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
      ((kernel_continuous Z Q.MS Q.matching u k).mono clear)
    refine ⟨D,fun x=>?_⟩
    simpa only [FVA2.GradedFar.Cart.ofPS,sent,PowerSeries.coeff_mk] using hD x.val x.property
  · intro p
    obtain ⟨C,hC,hp⟩ := compact V Q p K hK clear u
    exact ⟨C,hC,hp.mono fun r hr x=> hr none x⟩

include Q in
theorem future (h:ℕ) : ∃ α:Future G h, PaidFuture Fv P α θ :=
  futureWins Fv P Z Q.MS Q.matching (clock V Q) ((prepared V Q).connects (h+1) h (Nat.le_succ h))
    (classes V Q 2 (h+1))
end YM.Integration.GradedFar.AppointedDerivativeFrames
