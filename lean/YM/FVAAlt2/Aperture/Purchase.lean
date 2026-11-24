import YM.FVAAlt2.Aperture.Model
/-!
# Comparing on the absolute aperture. Adapt Integral.Window.passage (OURS cost) &
 Funds for outside/inside at fixed program.Crop.T separates FFT phases. No using any t′ estimate beyond this analytic identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Aperture
open Set Filter Finset MeasureTheory Function Lattice RG Precision Wilson Exterior Tree Bid
open PertExtension.Series Bulk Adjacent Order Assembly Marker Multi YM.Next.SectorChange Integral Gaussian
open Work.F03
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure Actual
open scoped Topology ContDiff Classical Matrix BigOperators ENNReal NNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P:PathData G}{p:Clip}{O:ChartRatio G}{S:StepData c f}
variable (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(w:S.Choices)(C:UnitCost)
variable {V:Type} [DecidableEq V] {R:Census V}(W:Bulk.Colors R G f)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=>Bulk.Joint S F (G:=G)
local notation "L"=>Precision.Key F G→ℝ
local notation "ρ" => C.enter
local notation "H" => F.Slice G
local notation "Q" => K.covariance F w
open Classical
variable (t:ℝ) (x:fieldDir G c 1)
local notation "ζ"=> Bulk.translated K F x
local notation:max "β_" z:max=> temperature (ρ z)
local notation:max "V_" z:max => sample z x
local notation:max "weight_" z:max y:max => Integral.weight (ρ z) 0 y W p P

-- translated Haar exactly for any measurable window, constant offset Absolute
local notation "μ"=> Gaussian.cloud (K.covariance F w)
variable (A: Set (F.Slice G))
def extent: Set (Precision.Key F G→ℝ) := swing K F t x ⁻¹' mouth O ∩ coast K F t x ⁻¹' A
def thermal (D:Lit R (F.Slice G)): Lit R L:= fun v=> Complex.ofReal (Real.exp (force (Q) v/2)* pay O (swing K F t x v)) • D (coast K F t x v)
lemma extent_meas (hs:MeasurableSet A):MeasurableSet (extent K F t x A):=by
   have h: Measurable (swing K F t x):= (swing_cont K F t x).measurable; exact (h (mouth_meas O)).inter ((Measurable.comp (release_continuous ..|>.measurable) h) hs)
-- reach arm
lemma freeing (hg : 0<t) (hw : MeasurableSet A ∧ A ⊆ covered K.jacobian (1:F.Slice G)) (D : Lit R H) (hD : Leaf.All D) :
    let d : Lit R L:= (extent K F t x A).indicator (thermal K F w t x D)
    Good μ d ∧ charge (F.order G) (A.indicator D)=Complex.ofReal (chartCost (K.covariance F w) t) • charge μ d := by
   intro d; let q := A.indicator D
   have hu := Covered hD hw.1
   suffices Ht : ∀ i:R.Mode, Integrable (atMark i d) μ ∧
      (charge (F.order G) q).part i=Complex.ofReal (chartCost (K.covariance F w) t)*(charge μ d).part i from
     ⟨fun i=>(Ht i).1,Marker.Poly.ext fun i=>(Ht i).2⟩
   intro i
   let ν:= (1:F.Slice G)
   let f := atMark i q
   have he : Envelope f := hu i
   obtain ⟨hp,heq⟩ := release_integral K.ratio ν f he.meas.stronglyMeasurable (by
      intro y hy; change (A.indicator D y).part i=0; rw [Set.indicator_of_notMem (show y∉A from fun hz=> hy (hw.2 hz))]; exact Poly.part_nil i)
   have hu := hp.mp (he.integrableC _)
   let e := (mouth O).indicator (fun y=>pay O y • f (release ν y))
   obtain ⟨ha,hr⟩ := at_price (K.covariance F w) (K.positive F w) hg (deposit K F t x) e
   let f' := fun z:L => Real.exp (Gaussian.force (K.covariance F w) z/2) • e (displaced (deposit K F t x) t z)
   have hq : f'=atMark i d := by
       ext1 z
       by_cases h : swing K F t x z∈mouth O
       · by_cases hs : coast K F t x z∈A
         · have hl : z∈extent K F t x A:= ⟨h,hs⟩
           unfold f' e d thermal; rw [← migrate, Set.indicator_of_mem h,mark_cut,Set.indicator_of_mem hl]; unfold f; simp_rw [smul_smul,Complex.real_smul]; unfold atMark q ν
           change _*((A.indicator D (coast K F t x z)).part i)=_
           rw [Set.indicator_of_mem hs]; rfl
         have hm : z∉extent K F t x A:= fun hz=>hs hz.2
         unfold f' e d; rw [mark_cut,← migrate,Set.indicator_of_mem h,Set.indicator_of_notMem hm]; change _ • (pay _ _ • atMark i (A.indicator D) (coast K F t x z))=_; rw [mark_cut, Set.indicator_of_notMem hs,smul_zero,smul_zero]
       unfold f' e d; rw [mark_cut,Set.indicator_of_notMem (show z∉extent K F t x A from fun hx=> h hx.1),← migrate,Set.indicator_of_notMem h,smul_zero]
   refine ⟨hq ▸ ha.mp hu,?_⟩
   rw [← Complex.real_smul]; refine heq.trans (hr.trans ?_)
   rw [components,← hq]


-- Absolute weight
local notation "κ"=> chartCost (K.covariance F w)
def priceT := ( chartCost (K.covariance F w) t * one_tag K F w (ρ t) 0 x )
def covers0 (A:Set (F.Slice G))(K:Kernel S p P O) := MeasurableSet A ∧ A⊆ covered K.jacobian 1 ∧ F.drape '' A⊆Integral.Min S
local notation "ξ"=> K.covariance F w
variable (B:Bed)(h:YM.FVAAlt2.Period.Rent.Right p P f B)
variable [Fintype V]
open Symmetry Laplace PertExtension.Series.Tested

def actual0 : Poly R:= charge (F.order G) ( A.indicator ((Actual.stack w (V_ t) β_ t (model (ρ t) 0 W K))∘F.drape))
def tale: Poly R:= (priceT K F w C t x:ℂ)⁻¹ • actual0 K F w C W t x A
lemma price_p (hg:0<t):0<priceT K F w C t x:= mul_pos (chartCost_pos ξ (K.positive F w) hg) (tag_pos K F w (ρ t) 0 x)
variable (hw : Well W)
include h hw
lemma purchase (ht:0<t)(hm:0<C.rating t)(ha:covers0 F A K): Good μ ((extent K F t x A).indicator (dims K F w C W t x)) ∧ charge μ ((extent K F t x A).indicator (dims K F w C W t x))= tale K F w C W t x A :=by
    let h₀ := ha.1
    let I:= extent K F t x A
    let φ:=((Actual.stack w (V_ t) (β_ t) (model (ρ t) 0 W K)) ∘ F.drape)
    obtain ⟨h₁,h₂⟩:= freeing K F w t x A ht ⟨ha.1,ha.2.1⟩ φ (fun i=>((Actual.tall w (sample t x) _ K.branches ( Integral.leaf_model K (ρ t) 0 W hw)) i).comp_env F.continuous_drape.measurable)
    let a:ℂ:= (one_tag K F w (ρ t) 0 x :ℝ); have hx:a≠0:=Complex.ofReal_ne_zero.mpr (tag_pos K F w _ 0 x).ne'; let U:= I.indicator (dims K F w C W t x)
    have hb:I.indicator (thermal K F w t x φ)=a • U:=by
       ext1 i; by_cases hg:i∈I
       · rw [Set.indicator_of_mem hg,Pi.smul_apply,show U i = _ from (Set.indicator_of_mem hg (dims K F w C W t x))]; unfold thermal φ;rw [Function.comp_apply,promised K F w C W t x B h i ht hm hw hg.1,uncharged _ (ha.2.2 (Set.mem_image_of_mem F.drape hg.2)) K.branches]; congr 1; unfold a one_tag; rw [div_eq_mul_inv,mul_comm] -- check
       unfold U; simp [hg]
    change Good μ (I.indicator _) at h₁; change _ = _ • charge μ (I.indicator _) at h₂
    rw [hb] at h₁ h₂; constructor
    · intro i;have hh: Integrable (a⁻¹ • atMark i (a • U)) μ := (h₁ i).const_mul _; rwa [mark_smul, smul_smul,inv_mul_cancel₀ hx, one_smul] at hh
    unfold tale actual0;change charge μ U= _ • charge (F.order G) (A.indicator φ); rw [h₂,smul_cost,smul_smul,smul_smul, mul_assoc,show (↑(chartCost ξ t):ℂ)*a= (↑(priceT K F w C t x):ℂ) from (Complex.ofReal_mul _ _).symm,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (price_p K F w C t x ht).ne'),one_smul]
end YM.Comparison.RG02.FVAAlt2.Aperture
