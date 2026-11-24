import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCutoffJets
import YM.Integration.WilsonMovingCompactTransfer
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCompactVolumes
open Filter Set Spec Table Extraction Next.UVStress
open PhysicalNext.Repeat.Legato
open PhysMS
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
    {order : Extraction.Order} {S : Table R.family.book}


open MeasureTheory FullVolume Function Lattice RG Wilson Extraction.Lease Difference Gaps Cells Asymptotics
open scoped ContDiff

open Metric Extra.WeakScaling
theorem comparison (simple:G.Simple)(F:Spec.Final R.family order S){n:ℕ}(v:Fin n→R.family.book.Token)
    (row:ℕ→Points n→ℂ)(earned:∀p,Cluster R.family .full p n
      (fun N=>lifted R.family N p v) (row p))
    {K:Set (Points n)}(compact:IsCompact K)(sep:K⊆conf n){δ:ℝ}(positive:0<δ):
    ∀ᶠi:ℕ in atTop,∀x∈K,dist (row (order.per i) x) (S.read x v)≤δ:=by
  obtain ⟨a,ha,haK⟩:=compact.exists_cthickening_subset_open (conf_open n) sep
  let V:=cthickening a K
  have thick:IsCompact V:=compact.cthickening
  have bought:=WilsonMovingCompactTransfer.measured R simple F v V thick haK δ positive
  rw [Extraction.Order.fused,Extraction.Order.late] at bought
  filter_upwards [bought,order.per.cofinal.eventually (room R.family.S compact)] with i paid interior
  intro x hx
  let z:=fun j:ℕ=>address (R.family.S.a (order.mesh j)) x
  have reaches:Tendsto (fun j=>tag (R.family.S.a (order.mesh j)) (z j)) atTop (𝓝 x):=
    (chosen (S:=R.family.S) x).comp order.mesh.cofinal
  have active:∀ᶠj:ℕ in atTop,tag (R.family.S.a (order.mesh j)) (z j)∈V:=by
    filter_upwards [(Metric.tendsto_nhds.mp reaches) a ha] with j hj
    exact mem_cthickening_of_dist_le _ _ _ K hx hj.le
  have just:x∈NoHit R.family.S (order.per i) n:=(no_wrap_hit R.family.S (interior hx)).2 (sep hx)
  have raw:= (earned (order.per i)).2 x just z order.mesh.choose order.mesh.cofinal reaches
  have cont:ContinuousAt (fun x=>S.read x v) x:=
    ((S.smooth_read F.room.kernel.smooth v).continuousOn x (sep hx)).continuousAt ((conf_open _).mem_nhds (sep hx))
  have limit:=raw.dist (cont.tendsto.comp reaches)
  apply le_of_tendsto limit
  filter_upwards [paid,active] with j funded inV
  exact (funded (z j) inV).le

theorem original {axis:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε s R T W):
    ∃row:(p n:ℕ)→(Fin n→R.family.book.Token)→Points n→ℂ,
      (∀p n:ℕ,∀v:Fin n→R.family.book.Token,Cluster R.family .full p n
        (fun N=>lifted R.family N p v) (row p n v)) ∧
      ∀(f:Extraction.Order)(ledger:Table R.family.book),Spec.Final R.family f ledger→
        ∀(n:ℕ)(v:Fin n→R.family.book.Token)(K:Set (Points n)),IsCompact K→K⊆conf n→
          ∀δ>0,∀ᶠi:ℕ in atTop,∀x∈K,dist (row (f.per i) n v x) (ledger.read x v)≤δ:=by
  obtain ⟨_,row,earned⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCutoffJets.original paid
  have clear:∀p n:ℕ,∀v:Fin n→R.family.book.Token,Cluster R.family .full p n
      (fun N=>lifted R.family N p v) (row p n v):=fun p n v=>((earned p n v).2.2 []).1
  exact ⟨row,clear,fun _ _ F n v _ compact sep _ pos=>
    comparison simple F v (fun p=>row p n v) (fun p=>clear p n v) compact sep pos⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCompactVolumes
end
