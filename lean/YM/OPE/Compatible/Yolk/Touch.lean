import YM.OPE.Compatible.Yolk.Book
/-!
 # Touch(B) budgets. Conditional response linear on full envelope of weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
-- adapt real variant Sizes
lemma push_Real {ι: Type*} [Countable ι] {β:ℝ} {p : ι→Config G f→ℝ} (hs : S.IsKernel β G) (h : Dominated p) (hp : ∀ i, Measurable (p i)) (V : Config G c) :
    HasSum (fun i => S.push β (p i) V) (S.push β (fun U => ∑' i, p i U) V) := by
  obtain ⟨q,hq,hb⟩ := h
  have hpn i := Integrable.of_bound ((hp i).aestronglyMeasurable (μ := prior G f)) (q i)
      (Eventually.of_forall (hb i))
  have hsn (i) := StepData.push_slice hs V (p i) (hpn i)
  obtain ⟨B,hB⟩ := hs.bound
  have hz i : (∫ U, ‖S.density β U V • p i U‖ ∂prior G f) ≤ B*q i := by
    rw [show B*q i = ∫ _ : Config G f, B*q i ∂prior G f by rw [integral_const]; simp]
    refine integral_mono (hsn i).norm (integrable_const _) fun U => ?_
    rw [norm_smul,Real.norm_of_nonneg (hs.positive U V)]
    exact mul_le_mul (hB U V) (hb i U) (norm_nonneg _) ((hs.positive U V).trans (hB U V))
  have he := hasSum_integral_of_summable_integral_norm hsn (Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun U => norm_nonneg _)) hz (hq.mul_left B))
  simpa only [StepData.push, smul_eq_mul, tsum_mul_left] using he

variable {X Y Z:Support f}
def stained (R:Rep G f)(X:Support f)(h:Config G f→ℝ) (i:Finset ℕ)(U:Config G f):= if (towY R.activities X i).Nonempty then Real.exp (R.exponent U) * (h U * R.activities.gasOccurrence R.p i U) else 0
section
variable (hR:R.Lawful σ C Λ E w) (h:Config G f→ℝ) (he:Envelope h)
include hR he
lemma sheer (X:Support f) : (∀ i, Measurable (stained R X h i)) ∧ Dominated (stained R X h):=by
    have hp:= hR.labels; obtain ⟨z,hz,H⟩:= Activities.gasSeries hp; constructor
    · intro i; unfold stained; split_ifs
      · refine (R.exponentEnv hR|>.exp|>.meas).mul (he.meas.mul ?_); unfold Activities.gasOccurrence; exact Measurable.ite (R.activities.admissible_borel R.p i) (Finset.measurable_fun_prod i fun j _=> hp.forced.meas j) measurable_const
      exact measurable_const
    obtain ⟨b,hb⟩:= he.cost; obtain ⟨v,hv⟩:= (R.exponentEnv hR|>.exp).cost
    have he : 0≤v:= (norm_nonneg _).trans (hv 1); have hB :0≤ b:= (norm_nonneg _).trans (hb 1)
    refine ⟨_,(hz.mul_left b).mul_left v,fun i U=>?_⟩; unfold stained; split
    · simp_rw [norm_mul]; exact mul_le_mul (hv _) (mul_le_mul (hb _) (H i _) (norm_nonneg _) hB) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) he
    rw [norm_zero]; exact mul_nonneg he (mul_nonneg hB ((norm_nonneg _).trans (H i U)))
end
abbrev smudge (R:Rep G f)(X:Support f)(U:Config G f):= ∑' i, stained R X (fun _=>1) i U
lemma pigment (R:Rep G f)(X:Support f)(h:Config G f→ℝ)(U:Config G f): (∑' i,stained R X h i U)= smudge R X U * h U:=by
   unfold smudge; rw [← tsum_mul_right]; apply tsum_congr; intro i; unfold stained; split
   · rw [one_mul]; ring
   exact (zero_mul _).symm
variable (hp:X ⊆ Y) (hR:R.Lawful σ C Λ E w)(h: Config G f→ℝ)(he:Envelope h)
local notation "A"=> R.activities
variable {ℳ:{b:Finset ℕ// Anchor R.activities X Y b}→Leaf S R}(k:{b:Finset ℕ// Anchor R.activities X Y b}→ℕ)
include hR hp he
set_option maxHeartbeats 200000 in
lemma spurts (hb:S.IsKernel R.beta G)(hf:∀ z, (ℳ z).turn=.gasKey (k z) ∧ ((A).forced (k z)).support=enrolY A Y z.val ∧
    ((A).forced (k z)).inventory= groupY A z.val ∧ (ℳ z).ingredient=court R Y z.val h)(V:Config G c)(hy:Y.Nonempty): HasSum (fun z:{b:Finset ℕ// Anchor R.activities X Y b}=> S.push R.beta (ℳ z).cicada V) (S.push R.beta (fun U=> smudge R X U*h U) V):=by
   obtain ⟨hx,hT⟩:= sheer hR h he X
   have hu : (fun x=>smudge R X x*h x)=fun x=> ∑' b, stained R X h b x:=funext fun i=>(pigment R X h i).symm
   rw [hu]; let f(b):=S.push R.beta (stained R X h b) V
   have hz:= (push_Real hb hT hx V).tsum_fiberwise (towY A Y)
   let g(i):= ∑' b:BitScope A Y i,f b.val
   have hj (i) : towY A X (towY A Y i)=towY A X i:=by
     ext j; unfold towY; simp only [mem_filter]; constructor
     · exact fun ⟨⟨h,_⟩,ha⟩=>⟨h,ha⟩
     exact fun ⟨h,ha⟩=>⟨⟨h,fun he=> ha (he.mono_right hp)⟩,ha⟩
   have hk(i)(hi:i∉ Set.range (fun x:{b:Finset ℕ// Anchor R.activities X Y b}=>x.val)): g i=0:=by
      refine (tsum_congr (f:=fun x:BitScope A Y i=> f x.val) (g:=fun _=> (0:ℝ)) fun j=>?_).trans tsum_zero
      have he:j.val∈ Set.univ:= Set.mem_univ j.val
      have hf : ¬ (towY A X j.val).Nonempty:=by
        intro ht; apply hi; refine ⟨⟨i,?_,?_⟩,rfl⟩
        · rw [← hj, j.property] at ht -- rewrite j issue
          exact ht
        obtain ⟨b,hb⟩:= j; clear ht he; subst i; ext; simp [towY]
      unfold f StepData.push; simp only [stained, if_neg hf,smul_zero,integral_zero]
   have hh(i:{b:Finset ℕ// Anchor R.activities X Y b}): g i.val=S.push R.beta (ℳ i).cicada V:=by
      have ht : Dominated (fun b:BitScope A Y i.val => stained R X h b.val):=by obtain ⟨U,hu,hb⟩:= hT; exact ⟨_,hu.comp_injective Subtype.val_injective, fun i=> hb _⟩
      rw [show g i.val= _ from (push_Real hb ht (fun i=>hx i.val) V).tsum_eq]
      apply congr_arg (fun f=>S.push R.beta f V); obtain ⟨h₁,h₂,h₃,h₄⟩:= hf i; funext U
      rw [filled (ℳ i) h₁ h₂ h₃ h₄ hy i.property.2 U, ← tsum_mul_left]; refine tsum_congr fun b=>?_ ; unfold stained; refine if_pos ?_; have hh:=i.property.1
      rw [← hj,b.property]; exact hh
   have hζ:= (Subtype.val_injective.hasSum_iff (g:=fun x:{b:Finset ℕ// Anchor R.activities X Y b}=>x.val) hk)|>.2 (show HasSum g _ from hz)
   exact hζ.congr_fun fun i=>(hh i).symm
end YM.PhysicalNext.Repeat.Aroma
