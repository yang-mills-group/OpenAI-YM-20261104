import YM.MatchingLedger.Periodical.Stalls

/-!
# Accessing the actual arrays on one small stencil (SD or measurement)

Outside not small; use port windows, keeping the external coarse log tilt.
Terms deterministic on these ports even if tags interact outside. These coordinates are only
for estimating conditional transfer (not editing marker book values).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio) (s : S.Choices)
    (hB : S.patch.Branches S.kernel G) (A : ChartRatio G) (Y : Chip (Page G c))

section purchase

def crawl (U : F.Slice G) := (tint G _).symm (boxLog A ∘ U)
def stage (R : Support c) (U : F.Slice G) := crop (located (nest F) R) (crawl F A U)
def column (R : Support c) (U : F.Slice G) : Chip (Meter F G) := Sum.elim (stage F A R U) Y
lemma binL_crank {ι α : Type} (u : Chip ι) (y : Chip α): binL (Sum.elim u y)=u:= rfl
lemma binR_crank {ι α : Type} (u : Chip ι) (y : Chip α): binR (Sum.elim u y)=y:= rfl
lemma at_stage (U : F.Slice G)(i : Needle F G): crawl F A U i =(boxLog A (U i.1)) i.2:= rfl
lemma onstage (R : Support c)(U : F.Slice G)(i : Needle F G): stage F A R U i= if nest F i∈R then crawl F A U i else 0:= by unfold stage; rw [crop_apply]; simp_rw [loc]

lemma clay (x: G.Color)(i:G.ColorIndex): ‖x i‖ ≤ ‖x‖:= by rw [Real.norm_eq_abs]; have he:= abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) x; simpa only [EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using he
lemma sliding {x y : Chip (Page G c)} (h:x=y) (R : Support c)(U : F.Slice G) : venue F (column F A x R U)= runway y := h ▸ rfl -- not needed

-- breath independent of U away from R
def fieldTest (R : Support c)(r : ℝ) : Set (F.Slice G) := {U | ∀ i : F.Free, area F i∈R → U i ∈ sector G r}
variable {A} {R : Support c}{r : ℝ} (hr:r ≤ dial A)

lemma inside_cov (G : Gauge){u : ℝ}(he : u≤r) : fieldTest (G:=G) F R u⊆fieldTest F R r := fun _ hi i hj=> sector_mono G he (hi i hj)
include hr in
lemma color_inside {U : F.Slice G} (hf : U∈fieldTest F R r)(i : Needle F G) (hi : nest F i ∈ R) :
    ‖crawl F A U i‖ ≤ r:= by rw [at_stage]; exact (clay ..).trans (mem_ball_zero_iff.mp (pedal hr (hf i.1 hi)).1).le
lemma stage_all (A : ChartRatio G) (U : F.Slice G): ‖stage F A R U‖≤1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=> by
  rw [onstage]; split
  · rw [at_stage]; exact (clay ..).trans (range_bound ..)
  simp
lemma crawl_all (A : ChartRatio G) (U : F.Slice G): ‖crawl F A U‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _=> (clay ..).trans (range_bound ..)
include hr in
lemma stage_range (h:0≤r) {U : F.Slice G} (hf : U∈fieldTest F R r) : ‖stage F A R U‖≤r := by
  refine (pi_norm_le_iff_of_nonneg h).2 fun i=>?_; rw [onstage]; split_ifs with he; exact color_inside F hr hf i he; rw [norm_zero]; exact h
include hr in
lemma column_range {U : F.Slice G} (hY:‖Y‖≤ r) (hf:U∈fieldTest F R r) : ‖column F A Y R U‖≤ r := joined (stage F A R U) Y (stage_range F hr ((norm_nonneg _).trans hY) hf) hY
lemma stage_inside (x : F.Slice G)(i : F.Free)(hi : area F i∈R) :
    tint G _ (stage F A R x) i= boxLog A (x i):=by
  ext j
  change stage F A R x (i,j) = _; rw [onstage]; rw [if_pos (show nest F (i,j)∈R from hi)]; rfl -- if not dite
include hr in
lemma here {U : F.Slice G} (hv:U∈fieldTest F R r) : equalInside S (F.drape U) (litter F (column F A Y R U)) R:= by
  intro i he; by_cases hh : i∈F.trunks
  · exact (F.on_tree _ ⟨_,hh⟩).trans (F.on_tree _ ⟨_,hh⟩).symm
  let j:F.Free:= ⟨i,hh⟩
  rw [show F.drape U i=U j from F.off_tree U j, show litter F (column F A Y R U) i= lights F (stage F A R U) j from F.off_tree (lights F (stage F A R U)) j, show lights F (stage F A R U) j = G.lieExp (tint G F.Free (stage F A R U) j) from rfl,stage_inside F (A:=A) U j (show area F j∈ R from he)]; exact (pedal hr (hv j he)).2.symm

include hr in
lemma sense : MeasurableSet (fieldTest (G:=G) F R r) := by
  rw [show fieldTest F R r= (⋂ i:F.Free, ⋂ (_ : area F i ∈ R), {x:F.Slice G | x i∈ sector G r}) from by ext x; simp [fieldTest]] -- equality annotation
  exact MeasurableSet.iInter fun i=> MeasurableSet.iInter fun (_:area F i∈ R)=> measurable_pi_apply i ((sector_open A hr).measurableSet)
-- Envelope and law
lemma crawling (A : ChartRatio G): Measurable (crawl F A):= by unfold crawl; apply Measurable.comp (g:=(tint G F.Free).symm) (Continuous.measurable (tint G F.Free).symm.continuous); exact measurable_pi_lambda _ (fun i=> (gauge_log A).comp (measurable_pi_apply _))
lemma script (A : ChartRatio G)(Y: Chip (Page G c)) (R : Support c) : Measurable (column F A Y R):= by unfold column stage; simp_rw [pieces, ← crop_true]; exact ((climb.continuous.measurable).comp ((cropMap _).continuous.measurable.comp (crawling F A))).add measurable_const
lemma coordinated (A : ChartRatio G)(t : ℝ) : Envelope (fun U=> t • crawl F A U):= by
  refine ⟨(crawling F A).const_smul (c:=t), ‖t‖,fun x=>?_⟩
  rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (crawl_all ..)

include hB hr
lemma compactDues {U : F.Slice G}(hv:U∈fieldTest F R r) (z : Site c) (hR:ribbon (S:=S) z ⊆ R) :
    Action.bill S (F.drape U) (runway Y) s z=dues S F G s z (column F A Y R U):=
  equal_price S hB (fun _ hi=> here F Y hr hv _ (hR hi)) s (fun _=> rfl)

-- no estimate asserting independence other than untapped from C1.
omit hB hr in
lemma consecutive (i : Needle F G) (he: arc F (Sum.inl i)⊆R) : ∀ z∈ depot F (Sum.inl i), ribbon (S:=S) z ⊆ R:= fun _ hh _ hz=> he (accumulate _ (belt S.patch) (belt S.patch) hh (near_root.mp hz))
lemma chart_amount {n : ℕ} (H : Budget G A n) (i : Needle F G) {U : F.Slice G}
    (h : U∈fieldTest F R r)(hY:‖Y‖≤r)(hh:r≤H.space S.patch S.kernel)(he:arc F (.inl i)⊆ R) (t : ℝ):
    Cooling.weight F (runway Y) t U= Real.exp (-t^2 * ∑ z∈depot F (.inl i), dues S F G s z (column F A Y R U))*
      untapped S {nest F i} (t^2) (F.drape U) (runway Y) := by
  let W:= depot F (Sum.inl i); let L:=column F A Y R U; let a (v) := bill S (F.drape U) (runway Y) v
  have hW(v : S.Choices) : total W (a v) = ∑ z∈W, dues S F G s z L:= Finset.sum_congr rfl fun z hz=> ((compactDues F v hB Y hr h z (consecutive F i he z hz))).trans
    (H.ignored F ((column_range F Y hr hY h).trans hh) v s z)
  unfold Cooling.weight probative untapped; rw [← opinion_scale]; apply congr_arg (opinion S (F.drape U))
  ext v; rw [total_split W]; rw [show total W _ = _ from hW v,mul_add,Real.exp_add]; rfl

end purchase
end YM.MatchingLedger.Periodical
