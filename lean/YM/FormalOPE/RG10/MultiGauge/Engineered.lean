import YM.FormalOPE.RG10.MultiGauge.Decomposition
/-!
 # Multi-mark conditional elimination diagram for an arbitrary fixed genuine Hierarchy

 A schedule in any fixed common parameter convention (e.g. choose parameter g_top when
 connecting at prior); powers by RG_08 supplying. Ordered elimination using conditional
 gaussian at every blocked interior and full conditional normalization denominator.
 Uses remaining diagram fields as passive slots: does NOT make any finer-scaling claim
 that the diagnostic footprints admit rerouting to only nearest-coarse value without
 carrying anything older. Spatial locality estimates of real construction neither
 consumed nor proved by this lemma. Gauge convention of Mark type retained by evaluator.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge.Blocking
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open StationaryMarks Stack Splice Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side}{L:Fabric G n}

-- recurse through *all* steps. Epoch-style local norms still need proof; calculation doesn't need them.
def transaction {n:Side} {L:Fabric G n} (T:Cloth L)(Λ:Law (Field T.choose)) (A W : Ticket (Field T.choose)): PowerSeries ℝ := match T with
 | .floor n h T=> enjoy Λ (tangent G (Cloth.floor n h T).choose.Bulk) A W
 | .inLayer (S:=S) (L:=M) (b:=H) (t:=t) (h:=hf) P C=>
   let d:= sector S H t hf M P C.choose
   transaction C (rest Λ d) (delivered Λ d (tangent G (Index S P)) A W) (reclose Λ d (tangent G (Index S P)) W) -- Λ coerces tail

lemma recorded {n:Side} {L: Fabric G n}(T:Cloth L) (Λ:Law (Field T.choose)) (A W: Ticket (Field T.choose))(h: incline W): transaction T Λ A W=enjoy Λ (tangent G T.choose.Bulk) A W:= by
 cases T with
 | floor=>rfl
 | @inLayer c _ S b t hf M P C=>
   rw [transaction]; exact (recorded C _ _ _ (born_transfer Λ (sector S b t hf M P C.choose) _ h)).trans ((preserve Λ (sector S b t hf M P C.choose) _ (tangent G _) _ A h).symm)
termination_by structural T

variable {P:ChartRatio G}(T:Cloth L)(w:L.Accounts→PowerSeries ℝ){F:L.LinksOn→ℝ}
local notation "Y"=> T.choose
local notation "Ξ"=> model L Y w

/-- genuine Schur protocol projection of multi-marked products: any **hierarchy observable**.
  This version for real-valued products; complex read via inversion-top algebra or splitting.
  Fixed geometry only including step procedure. Not claiming wiring estimates.
  -/
lemma full_tower (B: LocalRatio P)(hw:∀ i, 0<term (w i) 0)(H:Multipurpose L F):
 scene L Y w P F= transaction T (evidence _ (enough L Y w hw).entire) (imbed (F ∘ (Y).board)) (weight P Ξ):= by
 rw [recorded T _ _ _ (checked_up (U:=Ξ) B)]
 exact plan (enough L Y w hw) B (H.passes L Y)

theorem top_projection (B:LocalRatio P)(hw:∀ i, 0<term (w i) 0)(ht:w none=1){F: Wilson.Config G n→ℝ}(h:Orb.PreTest F):
 transaction T (evidence _ (enough L Y w hw).entire) (imbed (attending L F ∘ (Y).board)) (weight P Ξ) = PowerSeries.mk (Orb.diag (Orb.restrictedO F)):= by rw [← full_tower T w B hw (eligible L h), staple_root L w Y B hw ht h]
end YM.FormalOPE.RG10.MultiGauge.Blocking
