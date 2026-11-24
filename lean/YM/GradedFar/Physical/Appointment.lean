import YM.GradedFar.Physical.Homet
import YM.Integration.WilsonPositionHomogeneousCoefficients

/-! # Prices when buying an actual coupling-dependent (not crop-dependent) adjustment
  Implement Layer constructor using the original Warrant data on the field, & power estimate
  on the field. Applied at the eventual transported branch. -/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open Integration.WilsonPositionHomogeneousCoefficients
open private chairMove chairMove_eq from YM.GradedFar.Moving.Snow
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "α"=>Scale.Measure.adjust N.scheme N.criterion
include H
lemma phase_formula (p d : ℕ) (t : ℝ) : Continuation.atColumn (α d) p t=
    stand (∑ k∈Finset.range (p+1), t^k • letter N d k) := by
  let S:=Finset.range (p+1); have h0 : 0∈S:= by simp [S]
  unfold Continuation.atColumn;
  rw [← Finset.add_sum_erase (Finset.range (p+1)) (fun i=>(t:ℂ)^i • coeff i (α d)) h0, ← Finset.add_sum_erase (Finset.range (p+1)) (fun i=>t^i • letter N d i) h0,pow_zero,pow_zero,one_smul,one_smul,(recruited_j N M H).zero, show letter N d 0=0 from if_pos rfl,zero_add, stand];
  simp_rw [AddSubmonoidClass.coe_finsetSum]; apply congr_arg (1+·); apply Finset.sum_congr rfl; intro i hi
  rw [← Complex.ofReal_pow, ← positive N (purchased N H) d (Finset.mem_erase.mp hi).1]
  exact IsScalarTower.algebraMap_smul ℂ (t^i) _

variable (B : (d:ℕ)→ℝ→ Normalize.Change G d) (θ : ℝ → ℝ)
    (hθ : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1))
include hθ
lemma charged_layer (d : ℕ)
    (hB : ∀ᶠ r in τ, ∀ x, K r d x = J r d (stand (B d (θ r)) x))
    (hk : ∀ q, ∃ C : ℝ,0≤C ∧ ∀ᶠ t:ℝ in τ,
         ‖guide G d (B d t)-∑ n∈ Finset.range (q+1),t^n • guide G d (letter N d n)‖≤C*t^(q+1)) :
    Layer N θ (fun r=> stand (B d (θ r))) (next J d) (next K d) := by
  constructor
  · have hv : ∀ᶠ i : ℝ × (↥Growth.Small) in filed, ∀ x,
        let s':= resize i.1 i.2.val; K s' d x=J s' d (stand (B d (θ s')) x):=
      (span_nears filed N M Prod.fst (fun i:ℝ × ↥Growth.Small => i.2.val) tendsto_comap
        (Eventually.of_forall fun i=> i.2.property) H).eventually hB
    filter_upwards [hB,eventually_comap.mp hv] with r h hr s hs
    ext1 x; apply (J r d).injective
    let t:=resize r s; change J r d (stand _ ((K r d).symm (K t d x)))=J r d ((J r d).symm _)
    rw [←h, LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]; exact hr (r,⟨s,hs⟩) rfl x
  intro p
  let L:= LinearMap.toContinuousLinearMap (chairMove (G:=G) (d:=d))
  obtain ⟨C,hC,hf⟩:= hk p
  have hp := paid_reading simple θ hθ
  have ht : Tendsto θ τ τ := tendsto_nhdsWithin_iff.mpr ⟨Pose.tainted N M θ H hθ,hp.mono fun i hi=> hi.2.1⟩
  apply budget_of τ (C:=‖L‖*C*2^(p+1)) _ (hp.mono fun i h=>h.1.le)
  filter_upwards [hp,ht.eventually hf] with i hu h
  let X:Normalize.Change G d:=∑ k∈ Finset.range (p+1), θ i^k • letter N d k
  rw [phase_formula N M H]; change ‖chairs G d (stand (B d _) - stand X)‖ ≤ _
  rw [stand,stand] -- expand combine instead
  rw [show 1+(B d (θ i)).val-(1+X.val)=(B d (θ i)-X).val from (show 1+(B d (θ i)).val-(1+X.val)= _ - _ by abel),← chairMove_eq, map_sub]
  change ‖L ( _ - _ )‖ ≤ _; apply le_trans (ContinuousLinearMap.le_opNorm L (guide G d (B d (θ i))-guide G d X))
  have hx: guide G d X= _:=(show _=∑ k∈ Finset.range (p+1), θ i^k • guide G d (letter N d k) by unfold X; simp); rw [hx]
  have he:= pow_le_pow_left₀ hu.2.1.le ((le_abs_self _).trans hu.2.2.2) (p+1)
  exact ((mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left he hC)) (norm_nonneg _))).trans_eq (by rw [mul_pow]; ring)
end
end YM.FVA2.GradedFar.Physical
