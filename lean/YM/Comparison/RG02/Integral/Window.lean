import YM.Comparison.RG02.Integral.Bill
/-!
# Chart windows of integration and model comparison

 Offer customizable mask-aligned windows on the actual torus. (Statements allow even
 pathological V; useful when windows genuine for uniform Taylor etc.) Not smuggling
 price of their size outside. Work solely on the real Haar slice corresponding to THIS tag,
 conditional density factored. Windows are NOT imposed on Fk's Taylor coefficients.
 Expose each step cut.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Integral
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order YM.Next.SectorChange Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    {V : Type} [DecidableEq V] {R : Census V}

variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (g c₀ : ℝ) (x : fieldDir G c 1) (W : Bulk.Colors R G f)
local notation "I" => Precision.Key F G
local notation "Y" => F.Slice G
local notation "V'"=> sample g x
local notation "dγ" => Gaussian.cloud (K.covariance F t)
local notation "L"=> (I→ℝ)

variable (A : Set (F.Slice G))

def Reach (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (g : ℝ) (x : fieldDir G c 1) (A : Set (F.Slice G)): Prop := MeasurableSet A ∧ A ⊆ covered K.jacobian (repSample F g x)

/-- Preimage, **not** dropping restriction to mouth (period-aliased expansions otherwise). -/
def scope : Set L := offset K F g x ⁻¹' mouth O ∩ walk K F g x ⁻¹' A
lemma offset_cont : Continuous (offset K F g x) := by
   exact (Continuous.add continuous_const (show Continuous (tape (ι:=F.Free) (G:=G)) from gaugeCount.continuous)).const_smul g
lemma scope_meas (hs : MeasurableSet A) : MeasurableSet (scope K F g x A) := by
   have he:= (offset_cont K F g x).measurable
   exact (he (mouth_meas O)).inter ((Measurable.comp (release_continuous ..|>.measurable) he) hs)

def thermalTransform (D : Lit R Y) : Lit R L := fun v=> Complex.ofReal
    (Real.exp (Gaussian.force (K.covariance F t) v/2) * pay O (offset K F g x v)) • D (walk K F g x v)

-- Generic charge identity (can even choose windows separately by t). Strict meas & L¹ via
-- leaf envelope; lighter premise possible.
lemma passage (hg : 0<g) (hw : Reach K F g x A) (D : Lit R Y) (hD : Leaf.All D) :
    let d : Lit R L:= (scope K F g x A).indicator (thermalTransform K F t g x D)
    Good dγ d ∧ charge (F.order G) (A.indicator D)=Complex.ofReal (chartCost (K.covariance F t) g) • charge dγ d := by
   intro d; let q := A.indicator D
   have hu := Covered hD hw.1
   suffices H : ∀ i:R.Mode, Integrable (atMark i d) dγ ∧
      (charge (F.order G) q).part i=Complex.ofReal (chartCost (K.covariance F t) g)*(charge dγ d).part i from
     ⟨fun i=>(H i).1,Poly.ext fun i=>(H i).2⟩
   intro i
   let ν:= repSample F g x
   let f := atMark i q
   have he : Envelope f := hu i
   obtain ⟨hp,heq⟩ := release_integral K.ratio ν f he.meas.stronglyMeasurable (by
      intro y hy; change (A.indicator D y).part i=0; rw [Set.indicator_of_notMem (show y∉A from fun hz=> hy (hw.2 hz))]; exact Poly.part_nil i)
   have hu := hp.mp (he.integrableC _)
   let e := (mouth O).indicator (fun y=>pay O y • f (release ν y))
   obtain ⟨ha,hr⟩ := at_price (K.covariance F t) (K.positive F t) hg (start K F g x) e
   let f' := fun z:L => Real.exp (Gaussian.force (K.covariance F t) z/2) • e (displaced (start K F g x) g z)
   have hq : f'=atMark i d := by
       ext1 z
       by_cases h : offset K F g x z∈mouth O
       · by_cases hs : walk K F g x z∈A
         · have hl : z∈scope K F g x A:= ⟨h,hs⟩
           unfold f' e d thermalTransform; rw [displaced_eq, Set.indicator_of_mem h,mark_cut,Set.indicator_of_mem hl]; unfold f; simp_rw [smul_smul,Complex.real_smul]; unfold atMark q ν
           change _*((A.indicator D (walk K F g x z)).part i)=_
           rw [Set.indicator_of_mem hs]; rfl
         have hm : z∉scope K F g x A:= fun hz=>hs hz.2
         unfold f' e d; rw [mark_cut,displaced_eq,Set.indicator_of_mem h,Set.indicator_of_notMem hm]; change _ • (pay _ _ • atMark i (A.indicator D) (walk K F g x z))=_; rw [mark_cut, Set.indicator_of_notMem hs,smul_zero,smul_zero]
       unfold f' e d; rw [mark_cut,Set.indicator_of_notMem (show z∉scope K F g x A from fun hx=> h hx.1),displaced_eq,Set.indicator_of_notMem h,smul_zero]
   refine ⟨hq ▸ ha.mp hu,?_⟩
   rw [← Complex.real_smul]; refine heq.trans (hr.trans ?_)
   rw [components,← hq]

-- use a window where the chosen t has constant uniform weight. No other variation
-- discarded; hist real law over other t unchanged.
structure Trust (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (g : ℝ) (x : fieldDir G c 1) (b : Set (F.Slice G)) : Prop where
  seen : Reach K F g x b
  birth (y) : y∈b → S.likelihood (F.drape y) t = (count S:ℝ)⁻¹

variable (hT : Trust K F t g x A) (hg : 0< g) (Hw : Bulk.Well W)
include hg hT Hw
variable [Fintype V]
lemma identity :
    let H := model g c₀ W K
    let T' := (scope K F g x A).indicator (ambient K F t g x W)
    Good dγ T' ∧ charge (F.order G) (A.indicator (Actual.stack t V' (temperature g) H ∘ F.drape))=
      Complex.ofReal (wage K F t g c₀ x) • charge dγ T' := by
   intro H T'
   let D:= Actual.stack t V' (temperature g) H ∘ F.drape
   have he := passage K F t g x A hg hT.seen D (fun i=>((tall t V' (temperature g) K.branches (leaf_model K g c₀ W Hw)) i).comp_env F.continuous_drape.measurable)
   let a : ℂ:= Complex.ofReal (one_tag K F t g c₀ x)
   have ha : a ≠ 0 := by unfold a; exact_mod_cast (tag_pos K F t g c₀ x).ne'
   have hf : (scope K F g x A).indicator (thermalTransform K F t g x D)=a • T' := by
      funext z; by_cases hx : z∈ scope K F g x A
      · unfold thermalTransform T' D H
        rw [Set.indicator_of_mem hx,Pi.smul_apply,Set.indicator_of_mem hx, Function.comp_apply,
          actual_model K F t g c₀ x W z hg Hw hx.1, hT.birth (walk K F g x z) hx.2]; unfold a one_tag; rw [div_eq_mul_inv,mul_comm (count S:ℝ)⁻¹]
      simp [hx,T']
   change Good _ ((scope K F g x A).indicator _) ∧ _ at he
   rw [hf] at he
   refine ⟨by intro i; have hi:Integrable (a⁻¹ • atMark i (a • T')) _:= (he.1 i).const_mul _; rwa [mark_smul,smul_smul,inv_mul_cancel₀ ha,one_smul] at hi,?_⟩
   rw [he.2, smul_cost,smul_smul,paid_as]; unfold a; rw [Complex.ofReal_mul]
end YM.Comparison.RG02.Integral
