import YM.Comparison.RG02.Symmetry.Poles
/-! All-order local re-expression under the actual step signed/translation actions.
    Root norm transport after supports/cuts not asserted. Readers at the same degree j, finite
    period. Invoked on the chosen `t`; invariance across θ auxiliary, NOT a phase.
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

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F H : Forest S.ratio) (t u : S.Choices) (c₀:ℝ)
namespace Pole
variable (A : Set (F.Slice G)) (B : Set (H.Slice G)) (s : Signed) (b : Site c) (x y : fieldDir G c 1)
variable {W W': Bulk.Colors R G f} (r : ℕ)

local notation "τ"=> S.withinChoice s b t
section
local notation "Λ₀" => pad K F t c₀ x
local notation "Λ₁" => pad K H u c₀ y
/- Runtime from any window equivalence via Trial. -/
lemma returns (hA : A∈𝓝 1)(hB:B∈𝓝 1)(v:MeasurableSet A)(w:MeasurableSet B)
    (hX :∀ i:R.Mode, Serves K F c₀ W x D r A t i)(hY : ∀ i:R.Mode, Serves K H c₀ W' y D r B u i)
    (hj : ∀ g:ℝ,0<g→(wage K F t g c₀ x:ℂ) • portal K F t c₀ W x (fun _=>A) g = (wage K H u g c₀ y:ℂ) • portal K H u c₀ W' y (fun _=>B) g ) :
    Λ₀=Λ₁ ∧ Bulk.Fk K F t W x r=Bulk.Fk K H u W' y r := by
   have he(i:R.Mode) : ∀ j≤r,(Λ₀:ℂ)*detail (Bulk.Fk K F t W x r) i j=(Λ₁:ℂ)*detail (Bulk.Fk K H u W' y r) i j:= by
      let f := trial_scale (Λ₀:ℂ) ((hX i A (Set.Subset.refl _) v hA).2); let g:= trial_scale (Λ₁:ℂ) ((hY i B (Set.Subset.refl _) w hB).2)
      exact trial_gap (trial_congr (eventually_pos.mono fun j hj'=> by
         have h:= hj j hj'; rw [wages K F t j c₀ x hj',wages K H u j c₀ y hj',common_independent (G:=G) F H j] at h; have hC:= congrArg (fun z=> (Poly.part z i)) h
         simp_rw [Poly.part_smul, Complex.ofReal_mul, mul_assoc] at hC; exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (common_free H j (G:=G) hj' |>.ne')) hC) f) g
   have hx:= he R.quiet 0 (Nat.zero_le _); rw [tests_origin _ (Bulk.fk_unit ..),tests_origin _ (Bulk.fk_unit ..),mul_one,mul_one,Complex.ofReal_inj] at hx
   refine ⟨hx,(sym_coeff _ _ (Bulk.fk_sym ..) (Bulk.fk_sym ..)).2 ?_⟩
   intro i hi; ext q;have hy:= he q i hi; rw [hx] at hy
   exact mul_left_cancel₀ (show (↑Λ₁:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (pad_pos ..|>.ne')) hy
end
section
variable (w : Bulk.Well W)(w' : Bulk.Well W')(hw: CalendarEqv S s b W W')
include D hw w w'
lemma fit : pad K (Locations.forest s b F) t c₀ (shifts s b x)=pad K F (S.withinChoice s b t) c₀ x ∧ Bulk.Fk K (Locations.forest s b F) t W' (shifts s b x) r= Bulk.Fk K F (S.withinChoice s b t) W x r := by
    let H:=Locations.forest s b F; let a:= axis (G:=G) F s b
    obtain ⟨U,hU,hu,Y₀⟩:= Laplace.find K F c₀ W x D r w
    obtain ⟨Z,hZ,hz,Y₁⟩:= Laplace.find K H c₀ W' (shifts s b x) D r w'
    let I:= U ∩ a ⁻¹' Z; let J:= a '' I
    have hi:IsOpen I:= hu.inter (hz.preimage a.continuous);have hj:IsOpen J:=a.isOpenMap _ hi
    have he:a 1=1:= axis_zero ..
    have hy : (1:F.Slice G)∈I:= ⟨mem_of_mem_nhds hU,Set.mem_preimage.mpr (he.symm ▸ mem_of_mem_nhds hZ)⟩; have hq:(1:H.Slice G)∈J:=⟨1,hy,he⟩
    refine returns K D H F t (S.withinChoice s b t) c₀ J I _ _ r (hj.mem_nhds hq) (hi.mem_nhds hy) hj.measurableSet hi.measurableSet (fun i=>?_) (fun i=> ?_) (fun g=> portal_spin K F t _ g c₀ hw I)
    · exact smaller K H _ _ _ D _ _ _ _ _ (Set.image_subset_iff.mpr Set.inter_subset_right) (Y₁ t i)
    · exact smaller K F _ _ _ D _ _ _ _ _ (Set.inter_subset_left) (Y₀ _ i)

omit D w w' hw in
lemma pad_t : pad K F t c₀ x=pad K F u c₀ x := by
   apply mul_left_cancel₀ (common_free (G:=G) F 1 zero_lt_one |>.ne'); rw [← wages K F t _ c₀ x zero_lt_one,← wages K F u _ c₀ x zero_lt_one]; unfold wage; rw [office_choice K F t 1 c₀ x u]
lemma answer : pad K F t c₀ (shifts s b x)=pad K F t c₀ x ∧ Bulk.Fk K F t W' (shifts s b x) r=Bulk.Fk K F t W x r:= by
   obtain ⟨ha,hb⟩:= fit K D F t c₀ s b x r w w' hw; obtain ⟨hv,hl⟩:= Laplace.identical K F (Locations.forest s b F) t c₀ W' (shifts s b x) D r w'
   exact ⟨hv.trans (ha.trans (pad_t K F (S.withinChoice s b t) t c₀ x)),hl.trans (hb.trans (Bulk.fkChoice K F _ _ _ _ t))⟩
omit D hw w w' in
lemma price_zero : price K F t 0= 0:= by
    simp [price,Bulk.infrared,Bulk.classical,Assembly.jet]
    exact ContinuousMultilinearMap.map_zero _
lemma tariff: price K F t (shifts s b x) = price K F t x := by
    have hx:= (answer K D F t 0 s b x 0 w w' hw).1; rw [tax K F t (shifts s b x) 0,tax K F t x 0,price_zero,sub_zero,sub_zero] at hx
    exact Complex.ext (Real.exp_injective (mul_right_cancel₀ (pad_pos K F t 0 _|>.ne') hx)) (by simp [price])
open Orbit
lemma paired (i:ℕ) : ground K F t W' r i ∘ shifts s b=ground K F t W r i ∧ ∀ u:R.Mode, words K F t W' r u i ∘ shifts s b=words K F t W r u i := by
   constructor
   · funext x; rw [Function.comp_apply,ground, (answer K D F t 0 s b x r w w' hw).2,tariff K D F t s b x w w' hw]; rfl
   intro u; funext x; rw [Function.comp_apply, words, (answer K D F t 0 s b x r w w' hw).2]; rfl
end

def truncate (W : Bulk.Colors R G f) : Bulk.Colors R G f:= {W with mark:=0,power:=0}
omit [Fintype V] in
lemma truncate_well (h : Bulk.Well W) : Bulk.Well (truncate W):= by
      refine ⟨h.suppose_vac, fun i=> Assembly.GradeAt.grade_zero _, h.natural, fun _ _ _ _=>rfl,h.envelope,?_⟩
      intro i s; exact ⟨measurable_const, ‖(0:ℂ)‖, fun _=>le_rfl⟩
lemma carry (h : W.vac=W'.vac) : denominator (Bulk.Fk K F t W x r)=denominator (Bulk.Fk K F t W' x r):= by
    apply Join.both_parts; intro s v; simp_rw [denominator,bottom_value]; split_ifs
    next=> rw [Bulk.table,Bulk.table]; simp_rw [Bulk.clear]; unfold Bulk.geometric Bulk.fee Bulk.supplement; rw [h]
    next=> rfl
lemma vacant_drop (W : Bulk.Colors R G f): Orbit.ground K F t W r= Orbit.ground K F t (truncate W) r:= by funext i x; simp_rw [Orbit.ground,logVac, carry K F t x r (show W.vac=(truncate W).vac from rfl)]
include D
lemma season (w:Bulk.Well W) (h:∀y,W.vac y ∘ pull s (S.ratio.embed b)=W.vac y) (i:ℕ): Orbit.ground K F t W r i ∘ shifts s b= Orbit.ground K F t W r i:= by rw [vacant_drop K F t r W]; exact (paired K D F t s b r (truncate_well w) (truncate_well w) ⟨rfl,h,fun _ _=>rfl⟩ i).1
end Pole
end YM.Comparison.RG02.Symmetry
