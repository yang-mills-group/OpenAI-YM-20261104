import YM.OPE.Compatible.Minuet.Cork
/-! # Basin envelope on any torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ} {Ñ:ChartRatio G}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
lemma decks_env {ι:Type}[Countable ι] (v:Deckery R ι)(hv:∀ i j,Envelope (v.full i j))(hs:∀ i,Dominated (v.full i))(s:Signed)(l:ℕ):Envelope (v.honey s l):=by
   let g (i:Site f×ι) U:= if v.len i.2<l then v.full i.1 i.2 (pull s 0 U) else 0
   have hm i:Measurable (g i):=by unfold g; split_ifs; exact (hv i.1 i.2).meas.comp (continuous_pull ..|>.measurable); exact measurable_const
   refine ⟨Measurable.tsum hm,?_⟩; suffices h : Dominated g from h.bound
   choose z hz h using hs; have hp:Summable (uncurry z):= by
     apply Summable.of_norm; exact (summable_prod_of_nonneg fun _=>norm_nonneg _).2 ⟨fun i=> (hz i).norm,.of_finite⟩
   refine ⟨_,hp,fun i U=>?_⟩; unfold g; split; exact h ..; rw [norm_zero]; exact (norm_nonneg _).trans (h i.1 i.2 1)
private lemma worthPrice (G:Gauge)(u:G.El): ‖G.price u‖≤2:= by rw [Real.norm_eq_abs, abs_le]; have hz:=G.chord_price u; have hk:=G.chord_nonneg u; have hh:=G.chord_le_two u; constructor <;> nlinarith
variable (h:R.Lawful σ C Λ E w) (k:S.Choices) (V:Config G c)
include h
lemma tasteEnv (l:ℕ): Envelope (tasteU R l):=by
   refine (Envelope.const _).mul (Envelope.sum _ (fun i=>copeV R i l) fun i=>?_)
   unfold copeV groupsV
   have hs (n:ℕ)(J:ℕ→ Atom G n)(A:ℝ)(hp:SumBudget (fun i=>(J i).budget σ) A): Envelope ((emberY R J).honey i l):= by
      have hz:=(hp.2.1.mul_right (2^n))
      apply decks_env
      · intro x j; exact ⟨(Atom.unmasked_cont ..).measurable,_,fun U=> (J j).unmasked_bound U x⟩
      intro x; exact ⟨_,hz,fun j U=>le_trans (Atom.unmasked_bound ..) (mul_le_mul_of_nonneg_right ((J j).lower_budget _ h.paths.width) (pow_nonneg (show 0≤ (2:ℝ) by norm_num) _))⟩
   refine ((Envelope.const _).mul (((?_ : Envelope ((acid R).honey i l)).add (hs _ _ _ h.paths.three)).add (hs _ _ _ h.paths.four))).add (hs _ _ _ h.paths.two)
   have hp:= (Geo.lower_budget G R.path h.paths).2.1
   let z: Low→ℝ:=fun i=> 10*(|Low.mark R.path R.clip i| * Real.exp (σ*Low.length R.path i))
   have hz: Summable z:=hp.mul_left _
   have he i (x:Site f)(U:Config G f):‖(acid R).full x i U‖≤ z i:=by
      have ht:1≤ Real.exp (σ*Low.length R.path i):=Real.one_le_exp (mul_nonneg h.paths.width.le (Nat.cast_nonneg _))
      let p:=R.path; change ‖Low.mark _ _ _ * Low.plain p i x U‖≤ _; rw [norm_mul]; let A:=|Low.mark R.path R.clip i|
      have hc:‖Low.plain p i x U‖≤10:=by
         unfold Low.plain; cases i.2 with
         | inl _=> change ‖G.price _‖≤_; exact (worthPrice G _).trans (by norm_num)
         | inr j=> let u:= Low.left p i j; let v:=Low.right p i j; change ‖inner ℝ (u.atSite U x) (v.atSite U x)/2‖≤_
                   have hh:= (abs_real_inner_le_norm (u.atSite U x) (v.atSite U x)).trans (mul_le_mul (Slot.eval_norm ..) (Slot.eval_norm ..) (norm_nonneg _) zero_le_two)
                   rw [norm_div]; simp only [Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]; linarith only [hh]
      apply (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans; unfold z; change A*10≤_;rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (abs_nonneg _) ht) (by norm_num)
   exact decks_env (acid R) (fun x j=> ⟨measurable_const.mul (Low.plain_cont ..|>.measurable),_,he j x⟩) (fun x=>⟨z,hz,fun i=>he i x⟩) i l
lemma wickRoad (hp:S.patch.Branches S.kernel G)(l:ℕ)(I:Seats F): Envelope (Ruin R V l I k):=by
    have hh:Envelope (fun U=> R.beta * noiseTaylor S V U k):=(Envelope.const _).mul ((Envelope.const _).mul (Envelope.sum _ (fun i U=> G.price (V i*(S.prediction U k i)⁻¹)) fun i=>?_))
    · have ha (k:Config G f→ℝ)(hk: Envelope k): Envelope (fun U=> Real.exp (-tweak I k U)):=by
         have hz:=Env.along hk (steadyR I); exact (((show Envelope (tweak I k) by unfold tweak; simp_rw [sub_eq_add_neg]; exact hk.add hz.neg).neg)).exp
      exact (ha _ (tasteEnv h _)).mul (ha _ hh)
    exact ⟨G.continuous_price.measurable.comp (measurable_const.mul (((measurable_pi_apply i).comp (S.prediction_meas hp k)).inv)),2,fun _=>worthPrice G _⟩
end YM.PhysicalNext.Repeat.Aroma
