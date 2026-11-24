import YM.Integration.WilsonInvariantActionPosition
import YM.Integration.WilsonInvariantActionDoubleAdmission
import YM.Integration.WilsonExternalMeshMass

/-! The connected measured action response on the full signed two-site test,
with both original marks evaluated from the same retained mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPromotedPair
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Extraction Extraction.Order Spec
open Next.Rank PhysicalNext.Repeat.Legato RG17 FullVolume Table Climb Trace.Pilot Next.UVStress
open RGComparison.Core16
open WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals
open private tags from YM.Integration.WilsonInvariantActionIntegratedPair
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
    {F : Spec.Final R.family f S} {N p k : ℕ}

def parents (h : k ≤ N) (x : Fin 2→Site (R.family.side N p)) : Fin 2→Site (R.family.side N p) :=
  fun j=>(R.family.S.toDepth h p).embed ((R.family.S.toDepth h p).parent (x j))

def tested (h : k ≤ N) (a b : R.family.label 4) (φ : Test 2) : ℂ :=
  ∑ x : Fin 2→Site (R.family.side N p),WilsonExternalMeshMass.charge R.family φ x *
    posterior R (someSlices R.family.path.levels p) h a b (parents R h x)

private theorem volume_bill {n : ℕ} (φ : Test n) {r : ℝ} (hr : 0<r) :
    (∫x,‖dilate hr φ x‖)=∫x,‖φ x‖ := by
  have form (x : Points n) : ‖dilate hr φ x‖=(r^(4*n))⁻¹*‖φ (r⁻¹ • x)‖ := by
    change ‖(↑((r^(4*n))⁻¹):ℂ)*_‖=_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pow_pos hr _))]
  simp_rw [form]
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul_of_nonneg volume (fun x : Points n=>‖φ (r⁻¹ • x)‖) r (hR:=hr.le)
  rw [point_dimension,smul_eq_mul] at h
  simpa [inv_smul_smul₀ hr.ne'] using h.symm

private theorem row (L : Layout F) (r : ℝ) (w : Fin 2→R.family.label 4)
    {i : ℕ×ℕ} (h : k ≤ i.1) (hn : R.family.ref 4 ≤ i.1)
    (cut : (N p:ℕ)→Fin (N+1)) (x : Fin 2→Site (R.family.side i.1 i.2)) :
    let a := atRef L 4 r i (w 0)
    let b := atRef L 4 r i (w 1)
    posterior R (someSlices R.family.path.levels i.2) h a b (parents R h x) -
    posterior R (someSlices R.family.path.levels i.2) (Nat.le_of_lt_succ (cut i.1 i.2).isLt) a b x =
    WilsonMovingReportDisplacement.read R L r (fun _:Fin 2=>4) w i
      (WilsonReportCellProjection.ancestor (R.family.S.toDepth h i.2) ∘ (lift ∘ x)) -
    WilsonMovingReportDisplacement.read R L r (fun _:Fin 2=>4) w i (lift ∘ x) := by
  dsimp only
  let a:=atRef L 4 r i (w 0)
  let b:=atRef L 4 r i (w 1)
  have labels : tags R a b=(fun j:Fin 2=>⟨4,atRef L 4 r i (w j)⟩) := by
    funext j; fin_cases j <;> rfl
  have old : (wrap (R.family.side i.1 i.2) ∘ (lift ∘ x))=x := by ext j; simp
  have next : (wrap (R.family.side i.1 i.2) ∘
      (WilsonReportCellProjection.ancestor (R.family.S.toDepth h i.2) ∘ (lift ∘ x)))=parents R h x := by
    funext j; simp [Function.comp,WilsonReportCellProjection.exact_site,parents]
  rw [WilsonInvariantActionIntegratedPair.finite,WilsonInvariantActionIntegratedPair.finite]
  simp only [WilsonMovingReportDisplacement.read,old,next]
  change (_-single R a ((parents R h x) 0)*single R b ((parents R h x) 1))-
    (_-single R a (x 0)*single R b (x 1))=_
  rw [translation R hn a ((parents R h x) 0),translation R hn b ((parents R h x) 1),
    translation R hn a (x 0),translation R hn b (x 1)]
  change R.family.numeric i.1 i.2 (tags R a b) _ - _ - (R.family.numeric i.1 i.2 (tags R a b) _ - _) = _
  rw [labels]
  ring

theorem original (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) (L : Layout F)
    {B : ℕ} (hB : 0<B) (level : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (J : ℝ→PhysMS.tower S) (leading : PhysMS.Leading F J) {H : (Bel R.family.book).Hierarchy}
    (aligned : ∀ d:ℕ,∀ᶠ r in trail,PhysMS.Frame.obedient F H (J r) d)
    {g : ℝ→ℝ} (coupling : Coupling G g) (φ : Test 2) (power q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in trail, let m:=L.level r; let k:=WilsonInvariantActionPosition.berth R (2*power+q+1+25) m
      let β:=R.family.path.levels.clock.hatBeta m
      ∀ (hr : 0<r) (v : Fin 2→Free R.family 4) (w : Fin 2→R.family.label 4),
      (∀ j,‖v j‖ ≤ β^power) → R.family.ref 4 ≤ m → (∀ j,master L 4 r (w j)=J r 4 (v j)) →
      ∀ᶠ i:ℕ×ℕ in L.lens,∀ hk:k ≤ i.1,∀ cut:(N p:ℕ)→Fin (N+1),
      ‖tested R (p:=i.2) hk (atRef L 4 r i (w 0)) (atRef L 4 r i (w 1)) (dilate hr φ) -
        profile R cut (atRef L 4 r i (w 0)) (atRef L 4 r i (w 1)) (dilate hr φ) i.1 i.2‖
 ≤ ε*(g r)^q := by
  let M:ℝ:=(∫ x,‖φ x‖)+1
  have hm : 0<M := by dsimp [M]; positivity
  let o:=2*power+q+1
  have shift := WilsonInvariantActionPosition.purchased R hG pace L hB level g coupling J leading aligned
    (fun _:Fin 2=>4) (tsupport φ) φ.hasCompactSupport φ.tsupport_subset power 0 q o
    (by dsimp [o]; omega) (div_pos he hm)
  filter_upwards [shift,coupling.positive] with r moved gp
  dsimp only
  intro hr v w hv live hw
  have step:=moved v w hv (fun _=>live) hw
  let T := dilate hr φ
  have mass := (WilsonExternalMeshMass.funded R.family f T T.continuous T.hasCompactSupport
    (show (0:ℝ)<1 by norm_num)).filter_mono L.certified
  filter_upwards [step,mass] with i cart bill
  intro hk cut
  have hn := live.trans ((WilsonInvariantActionPosition.arrival R (o+25) (L.level r)).1.le.trans hk)
  let a:=atRef L 4 r i (w 0)
  let b:=atRef L 4 r i (w 1)
  let y:=fun x : Fin 2→Site (R.family.side i.1 i.2)=>posterior R (someSlices R.family.path.levels i.2) hk a b (parents R hk x)
  let z:=fun x : Fin 2→Site (R.family.side i.1 i.2)=>posterior R (someSlices R.family.path.levels i.2)
    (Nat.le_of_lt_succ (cut i.1 i.2).isLt) a b x
  let c:=fun x : Fin 2→Site (R.family.side i.1 i.2)=>WilsonExternalMeshMass.charge R.family T x
  have single_cost (x : Fin 2→Site (R.family.side i.1 i.2)) :
      ‖c x*(y x-z x)‖ ≤ ‖c x‖*(ε/M*(g r)^q) := by
    by_cases zero : T (cells R.family i.1 i.2 x)=0
    · have cx : c x=0 := by simp [c,WilsonExternalMeshMass.charge,zero]
      simp [cx]
    have support : r⁻¹ • tag (R.family.S.a i.1) (lift ∘ x)∈tsupport φ := by
      apply subset_tsupport
      intro vanish
      apply zero
      change (↑((r^(4*2))⁻¹):ℂ)*φ (r⁻¹ • cells R.family i.1 i.2 x)=0
      change φ (r⁻¹ • cells R.family i.1 i.2 x)=0 at vanish
      rw [vanish,mul_zero]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    dsimp only [y,z,a,b]
    rw [row R L r w hk hn cut x]
    simpa only [pow_zero,one_mul] using cart hk (lift ∘ x) support
  have total : ∑ x,‖c x‖ ≤ M := by
    simpa only [c,T,volume_bill φ hr,M] using bill
  have identity : tested R (p:=i.2) hk a b T - profile R cut a b T i.1 i.2 =
      ∑ x,c x*(y x-z x) := by
    simp only [tested,profile,c,y,z,WilsonExternalMeshMass.charge,Finset.mul_sum,mul_sub,Finset.sum_sub_distrib,mul_assoc]
  change ‖tested R (p:=i.2) hk a b T - profile R cut a b T i.1 i.2‖ ≤ _
  rw [identity]
  calc ‖∑ x,c x*(y x-z x)‖ ≤ ∑x,‖c x*(y x-z x)‖ := norm_sum_le _ _
    _ ≤ ∑x,‖c x‖*(ε/M*(g r)^q) := sum_le_sum fun x _=>single_cost x
    _ = (∑x,‖c x‖)*(ε/M*(g r)^q) := (sum_mul ..).symm
    _ ≤ M*(ε/M*(g r)^q) := mul_le_mul_of_nonneg_right total (by positivity)
    _ = ε*(g r)^q := by field_simp

end YM.Integration.WilsonInvariantActionPromotedPair
