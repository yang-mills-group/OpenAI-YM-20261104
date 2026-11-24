import YM.FormalOPE.RG10.Sync.Computer
/-!
 # Step-data genuinely on the same Episode. Choose actual ℝ layouts with location.S
     and price coordinate conversions and mask costs distinctly. Regulator geometry
     as in L. These results specifically before ratio change in field coordinates;
     all log links use common g. Use adapters for other choices. Not proving any
     physical identity here. Future Bulk orientation estimates still hypotheses.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open PertExtension Precision Inherit Push.Loops Chart Lattice RG PowerSeries BlockGauge MultiGauge.Blocking Fabric
open Route PowerSeries Finset MarkovChain MarkovChain.Warp MarkovChain.Router OpenSlots OpenSlots.Quadratic
open scoped Classical ContDiff Topology BigOperators ENNReal Matrix.Norms.Frobenius
variable {G: Gauge} {c f : Side}
variable {S: StepData c f}
variable {I B:Type}[Fintype I] [Fintype B]
variable (J:ChartRatio G) (t:S.Choices)(P:Inside S.ratio)
variable (L:Layout I (Flats G f))(Q: Layout B (Flats G c))
-- layout consistency across levels.
local notation "F"=> Cross (G:=G) S P
local notation "d"=> OpenSlots.extend (G:=G) P
local notation "b"=> blankRight (G:=G) P -- projection out of pair
-- dynamic U is real kernel germ.R
 def collapse (x:Flats G f)(i:Blocking.Index S P) : G.Color:= x i.val
 def threadTo : Flats G f →ₗ[ℝ] F where toFun := fun u=> collapse P u; map_add' _ _:=rfl; map_smul' _ _:=rfl
-- S parameter maybe collapse P
lemma pursue (x:F): threadTo P (d x)=x:= by ext1 i; change OpenSlots.extend P x i.val=x i; simp [OpenSlots.extend, i.property]; rfl -- type multiple

variable (w:PowerSeries ℝ)(U:Unmasked G f)
local notation "W"=> gated P U t w
-- Prop intangible dependent type; avoid local variable h
local notation "B0"=> Flats G c
 def shelter (h:(core W).RespectsPrice): Flats G f × Flats G c →ₗ[ℝ] Flats G f:= LinearMap.fst ..+ (OpenSlots.extend P) ∘ₗ (skew _ h) ∘ₗ LinearMap.snd ..
-- replot pulls FULL fine (not zero pinned before pulling); vertices coded on full & have no phantom pins.
 def Engine (h:(core W).RespectsPrice): Episode I B (Space F):= station h.inner L Q (OpenSlots.extend P) (threadTo P) (boost (Quadratic.center _ h) (receipt P t J w U)) (shelter t P w U h)

-- pass weight as factored price.Q
lemma stationed (h:(core W).RespectsPrice) (A:Ticket (F × B0)): Quadratic.uptake _ (tangent G (Blocking.Index S P)) h A= simpleMean h.inner (tangent G (Blocking.Index S P)) (boost (center _ h) A):= by
 apply PowerSeries.ext; intro i; unfold Quadratic.uptake simpleMean boost throughPrice; simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk, LinearMap.toAddMonoidHom_coe, PowerSeries.coeff_map]; rfl
-- tangent blocked filling
lemma sway (h:(core W).RespectsPrice): (blankRight P) ∘ₗ (center _ h) = (shelter t P w U h) ∘ₗ (d).prodMap (LinearMap.id (R:=ℝ) (M:=B0)):= by apply LinearMap.ext; rintro ⟨x,y⟩; change d (x+ _)= d x + d _ ; rw [map_add]; rfl
include L Q
lemma available (hJ:LocalRatio J) (u: incline U.W)(h:(core W).RespectsPrice)(A:Ticket (Flats G f)):
 digital Q (Broadcast P t J w U h (boost (blankRight P) A))= (Engine J t P L Q w U h).floats (digital L A):= by
 let ν:=tangent G (Blocking.Index S P); let Z:=boost (center _ h) (receipt P t J w U)
 have hf: incline Z:= preserve_boost _ (OpenSlots.along hJ w u)
 unfold Broadcast Engine fit; rw [stationed, _root_.map_mul (boost _), OpenSlots.boosts,sway,stationed]; exact (current h.inner L Q d _ _ _ (pursue P) ν hf A).symm
end YM.FormalOPE.RG10.Sync
