import YM.Comparison.RG02.Symmetry.Cubic
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
/-!
# Transport of actual predictor law, marked slices and Fk data under signed symmetries

Here and throughout a marker denotes the very input driver in W. Rotating the marked rule
means making an exact different packet list and supplying its equality on FULL U; equal field
stencils at transformed offsets can thus use this on the same admissible physical trajectory. We
use actual `Turn.glide` on slice -- do not infer permanence of total norm/log under that operation.
Additional signed and translation estimates on the numerical reclosures remain. Not about RP itself
or Torus quotient/cuffed masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested YM.Push.SectorMeasure
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace
open YM.AnalyticBridge.GaussianFieldAlignment YM.PhysicalNext.Repeat
open YM.AnalyticNext.QuarticMatch.Joint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {V : Type} [DecidableEq V] {R : Census V}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O)
  (F : Forest S.ratio) (t : S.Choices)
namespace Pole
variable (s : Signed) (b : Site c) (x : fieldDir G c 1)
private def flip (i : (Locations.forest s b F).Free) (x:G.El) : G.El:= if s.flip i.val.2 then x⁻¹ else x
private lemma flip_twice (i:(Locations.forest s b F).Free) : Involutive (flip (G:=G) F s b i):= by unfold Involutive flip; split <;> simp [*]
private def undo (y:(Locations.forest s b F).Slice G) : F.Slice G:= fun i=> flip F s b ((Locations.free s b F).symm i) (y ((Locations.free s b F).symm i))
lemma glide_flip (x:F.Slice G) (i:(Locations.forest s b F).Free): Turn.glide s b F x i=flip F s b i (x (Locations.free s b F i)):= rfl
def axis : F.Slice G≃ₜ(Locations.forest s b F).Slice G where
  toFun := Turn.glide s b F
  invFun := undo F s b
  right_inv x := by funext i; rw [glide_flip,undo,Equiv.symm_apply_apply,flip_twice]
  left_inv x := by
    funext i; simp only [undo,glide_flip,Equiv.apply_symm_apply]; exact flip_twice F s b _ _
  continuous_toFun := continuous_pi fun i=> by simp_rw [glide_flip,flip]; split <;> fun_prop
  continuous_invFun := continuous_pi fun i=> by unfold undo flip; split <;> fun_prop
lemma moving : MeasurePreserving (axis (G:=G) F s b) (F.order G) ((Locations.forest s b F).order G) := Turn.forest_toll ..
lemma axis_zero: axis F s b (1:F.Slice G)=1 := by
   change Turn.glide s b F 1= _; funext; unfold Turn.glide; split <;> simp

section atStep
variable (C D: Lit R (Config G f)) (U' : Config G c) (β : ℝ) (A : Set (F.Slice G))
variable (h : D ∘ pull s (S.ratio.embed b)=C) (hK : S.patch.Branches S.kernel G)
include h hK
lemma stack_oriented (U : Config G f): stack t (pull s b U') β D (pull s (S.ratio.embed b) U)=stack (S.withinChoice s b t) U' β C U:= by
   unfold stack taggedKernel; rw [S.mass_channel hK,S.prediction_channel hK,S.noise_channel,← Function.comp_apply (f:=D),h]
lemma backs : charge ((Locations.forest s b F).order G) ((axis F s b '' A).indicator (stack t (pull s b U') β D ∘ (Locations.forest s b F).drape))=charge (F.order G) (A.indicator (stack (S.withinChoice s b t) U' β C ∘ F.drape)) := by
   let q:=axis (G:=G) F s b; let p:= (q '' A).indicator (stack t (pull s b U') β D ∘ (Locations.forest s b F).drape)
   have he:p ∘ q=A.indicator (stack (S.withinChoice s b t) U' β C ∘ F.drape) := by
      funext y; by_cases hz:y∈A; swap
      · rw [Set.indicator_of_notMem hz]; exact Set.indicator_of_notMem (show q y∉q '' A from by rintro ⟨u,hu,e⟩; exact hz ((q.injective e) ▸ hu)) _
      unfold p; rw [Function.comp_apply,Set.indicator_of_mem (Set.mem_image_of_mem _ hz),Set.indicator_of_mem hz, Function.comp_apply,show (Locations.forest s b F).drape (q y)=pull s (S.ratio.embed b) (F.drape y) from Turn.forward ..]; exact stack_oriented t s b C D U' β h hK _
   rw [← he]; ext z; rw [components,components]; exact ((moving F s b).integral_comp q.measurableEmbedding (atMark z p)).symm

-- entire Density under all tags. Pointwise hypothesis re-expressed D not splitting mark inputs.
include F
lemma keep (hC : Leaf.All C) (hD : Leaf.All D) (hh : GaugeInvariant C) (hg : GaugeInvariant D) : Push S β D (pull s b U')=Push S β C U' := by
    rw [agreed (pull s b U') β hK hD,agreed U' β hK hC]; conv_rhs=> rw [← Equiv.sum_comp (S.withinChoice s b)]
    apply Finset.sum_congr rfl; intro i _; rw [pack (Locations.forest s b F) i _ _ hK hD hg,pack F (S.withinChoice s b i) _ _ hK hC hh]; simpa using backs F i s b C D U' β Set.univ h hK
end atStep
lemma loop_spin (X' : Config G f) (P: PathData G) : loop P (pull s (S.ratio.embed b) X')=loop P X':= by
  unfold loop Patch.average; apply congr_arg; conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  apply Finset.sum_congr rfl; intro i _; dsimp only; rw [pull_pull,translate_by (s*i) (affine s (S.ratio.embed b) 0),uncut_translate]; rfl

variable (S) in
structure CalendarEqv (W W' : Bulk.Colors R G f):Prop where
  marker_pay : W.power=W'.power
  reworn (u : ℝ) : W'.vac u ∘ pull s (S.ratio.embed b)=W.vac u
  labeled (i : Hot R)(u:ℝ) : W'.mark i u ∘ pull s (S.ratio.embed b)=W.mark i u

variable {s b}
variable {W W': Bulk.Colors R G f} [Fintype V] (g c₀:ℝ)
  (he : CalendarEqv S s b W W')
include he
lemma represents: model g c₀ W' K ∘ pull s (S.ratio.embed b)=model g c₀ W K:= by
   have hz i u : W'.mark i g (pull s (S.ratio.embed b) u)=W.mark i g u:=congr_fun (he.labeled i g) u
   funext u; unfold model Integral.weight localClassic markedLog; rw [Function.comp_apply]; rw [main_pull,show W'.vac g (pull s (S.ratio.embed b) u)=W.vac g u from congr_fun (he.reworn g) u,loop_spin (S:=S)]; simp_rw [he.marker_pay,hz]
omit he [Fintype V] in
lemma taken : sample g (shifts s b x)=pull s b (sample g x):= by unfold sample; rw [← map_smul]; exact rep_shifts ..
lemma portal_spin (A : Set (F.Slice G))(h:0<g) : (wage K (Locations.forest s b F) t g c₀ (shifts s b x):ℂ) • portal K _ t c₀ W' (shifts s b x) (fun _=> axis F s b '' A) g=(wage K F (S.withinChoice s b t) g c₀ x:ℂ) • portal K F (S.withinChoice s b t) c₀ W x (fun _=> A) g := by
    unfold portal; rw [smul_smul,smul_smul,mul_inv_cancel₀ (show (↑(wage K (Locations.forest s b F) t g c₀ (shifts s b x)):ℂ) ≠0 from Complex.ofReal_ne_zero.mpr (wage_pos K _ t g c₀ _ h |>.ne')),one_smul,mul_inv_cancel₀ (show (↑(wage K F (S.withinChoice s b t) g c₀ x):ℂ)≠0 from Complex.ofReal_ne_zero.mpr (wage_pos K F _ g c₀ x h |>.ne')),one_smul]; rw [taken]; exact backs F t s b _ _ _ _ A (represents K g c₀ he) K.branches
end Pole
end YM.Comparison.RG02.Symmetry
