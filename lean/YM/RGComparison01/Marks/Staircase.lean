import YM.RGComparison01.Marks.Story
import YM.RGComparison01.Marks.Slate
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
/-!
# Real parameter arc for the normalized log transfer

 An output exponent carrying precisely the same conditional denominator as
 the moments of analytic field tests. No subtracting volume-sized terms. -/
namespace Staircase
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion
variable [Fintype ι] (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R)
local notation "Xp"=> Tickets (Palette.sign M S)
-- ANC apertures for real Fine partner. No inclusion of actual unmarked extensive scalar forecast.
def grows (M:ι→Lotus.Leaf R) := ∀ i, ∃ k,(M i).turn = Wing.logKey k
omit [Fintype ι] in
lemma included_test (h:grows M)(i:Xp) (q:ℕ): q∉ (team M i).gasDue := by
   intro hv; obtain ⟨s,hs,hF⟩:= (Team.asked _ _).1 hv
   obtain ⟨j,hj,rfl⟩:= Finset.mem_image.mp hs; obtain ⟨l,hl⟩:=h j; rw [hl] at hF; cases hF
-- exact denominator any such VIRGIN model not assertions of normalization. RHS formula independent of K representation on LOG test.
def cardTest (S:StepData c f) (p : Finset ι) (U: Config G f): ℝ:= if h:Draft (Palette.sign M S) p then (team M ⟨p,h⟩).ingredients U*(∏ i∈p,g i) else 0
omit [Fintype ι] in
lemma setModel (V:Config G f): cardTest M g S ∅ V=1:= by
  unfold cardTest; rw [dif_pos (show Draft (Palette.sign M S) ∅ from (Tickets.none _).2)]; simp only [Team.ingredients,Palette.team,image_empty,prod_empty,mul_one]
omit [Fintype ι] in
lemma test_given (h:grows M)(i:Xp)(U:Config G f): (R.eval * cardTest M g S i.val) U= (team M i).cicada U*(∏ j∈i.val,g j):=by
   unfold cardTest Team.cicada; rw [Pi.mul_apply,dif_pos i.2]
   let Z:=team M i; have he:Z.gasDue=∅:= eq_empty_iff_forall_notMem.mpr (included_test M h i)
   have hx p: Z.bun p U= Z.ingredients U* R.activities.gasOccurrence R.p p U:= by
      unfold Team.bun Team.bill Activities.gasOccurrence; split
      next _=> rw [he,if_pos (empty_subset _), sdiff_empty]
      next _=> rw [mul_zero]
   change R.eval U*(Z.ingredients U*_)= Real.exp _ * (∑' p,Z.bun p U)*_; simp_rw [hx]; rw [tsum_mul_left]; unfold RG.Rep.eval Activities.gas; ring
local notation "UnitP" => (S.push R.beta R.eval)
def projection (q:Config G c) (p: Finset ι):= S.push R.beta (R.eval * cardTest M g S p) q / UnitP q
include H
lemma carried (h:grows M)(p:ℝ) (X:Finset ι)(V:Config G c):
    S.push R.beta (buy M (ways g p X) S) V= ∑ i:Xp, click i.val (S.push R.beta (R.eval * cardTest M g S i.val) V) p X:=by
   let W (i:Xp):= R.eval * cardTest M g S i.val
   have he : S.IsKernel R.beta G:= S.isKernel (funds_branch H.laws.intake.ready) _
   have hv i: Integrable (W i) (Wilson.prior G f):= by
     rw [show W i= _ from funext (test_given M g h i)]; exact ((team M i).sells H.laws.intake.cap|>.1.integrable _).mul_const _
   have ht: buy M (ways g p X) S= fun U=> ∑ i:Xp, click i.val 1 p X * W i U:=by
     funext U; unfold buy; refine Finset.sum_congr rfl fun i _=> ?_; rw [show W i U= _ from test_given M g h i U]; unfold Palette.sale; rw [amplitudes]; unfold click; split_ifs <;> ring
   unfold StepData.push; rw [ht]; simp_rw [smul_eq_mul, Finset.mul_sum, mul_left_comm (S.density _ _ _ : ℝ) (click ..)]; rw [integral_finsetSum]
   · refine Finset.sum_congr rfl fun i _=>?_ ; rw [integral_const_mul]; change _ * S.push R.beta (W i) V= click i.val (S.push R.beta (W i) V) p X; unfold click; split_ifs<;> ring
   exact fun i _=> (StepData.push_slice he V _ (hv i)).const_mul _

lemma in_record (h:grows M)(X:Finset ι)(V:Config G c): Switch.jet (fun t p=> S.push R.beta (Palette.buy M (Palette.ways g t p) S) V / UnitP V) X= projection M g (S:=S) V X:=by
   let P (i:Xp):= projection M g (S:=S) V i.val
   let v:= UnitP V
   rw [show (fun t p=> S.push R.beta _ V/UnitP V)=∑ i:Xp, click i.val (P i) from ?_]
   swap
   · funext t p; rw [Staircase.carried M g H h]; simp_rw [Finset.sum_apply]; rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _=>?_ ); unfold P projection Switch.click; split_ifs <;> ring
   rw [Slate.family univ (fun i:Xp=> click i.val (P i)) (fun i=> |P i|) (fun i _=> paidClick _ (abs_nonneg _) (fun _=>le_rfl)), Finset.sum_apply]
   simp_rw [(modelClick _ _).exact]; unfold projection
   by_cases hx : Draft (Palette.sign M S) X
   · let A:Xp:= ⟨X,hx⟩; rw [sum_eq_single_of_mem A (mem_univ A),Switch.bench,if_pos (show X=A.val from rfl)]
     · rfl
     intro i _ hi; exact if_neg (fun hk=>hi (Subtype.ext hk.symm))
   have he: cardTest M g S X=0:= funext fun _=> dif_neg hx
   rw [sum_eq_zero,he,mul_zero,StepData.push]
   · simp
   intro i _; exact if_neg (fun (h': X=i.val)=> hx (h'.symm ▸ i.2))
lemma zap (h:grows M)(V:Config G c): S.push R.beta (Palette.buy M (Palette.ways g 0 ∅) S) V= UnitP V:=by
   rw [carried M g H h]; let Z:=Tickets.none (Palette.sign M S)
   rw [sum_eq_single Z]; swap
   · intro i _ hi; exact if_neg (fun ht=> hi (Subtype.ext (Finset.Subset.antisymm ht (empty_subset _))))
   swap
   · simp
   unfold Switch.click; rw [if_pos (show Z.val ⊆ ∅ from le_refl _)]
   change (0:ℝ)^(Finset.card (∅:Finset ι)) * S.push R.beta (R.eval*cardTest _ _ _ ∅) V= _; rw [show cardTest M g S ∅=1 from funext (setModel M g),card_empty,pow_zero,one_mul,mul_one]

-- ARC givens hold from Story. Need list path once only before K budget reduction.
local notation "P0"=> Heron.bouquet M g H (χ:=χ)
structure TrueSector (F : Config G c→ Ways ι) (P:BudgetPoint) : Prop where
   active (V:Config G c)(h:flags P.threshold V=∅): 0<UnitP V ∧ ∀ t∈Set.Icc (0:ℝ) 1,∀ x, UnitP V *Real.exp (F V t x)= S.push R.beta (Palette.buy M (Palette.ways g t x) S) V
-- regardless of pollen lengths.
lemma service (h:grows M) (P:BudgetPoint) (K:ℝ→Finset ι → Code G c) (Z:Activities G c)
    (F':Config G c→ℝ) (hF:∀ V,0<F' V) (hc:∀ V (t:ℝ),t∈ Set.Icc 0 1 → ∀ x,
       F' V*Real.exp (Heron.bouquet M g H (χ:=χ) V t x)*(black Z (K t x)).gas P V= S.push R.beta (Palette.buy M (Palette.ways g t x) S) V) : TrueSector M g (S:=S) (P0) P := by
   constructor; intro V hV
   have he t (hp:t∈ Set.Icc (0:ℝ) 1) k: F' V * Real.exp (P0 V t k)= _:= Eq.trans (b:=F' V*Real.exp (P0 V t k)*(black Z (K t k)).gas P V) (by rw [Activities.gas_one _ _ hV,mul_one]) (hc V t hp k)
   have ht : F' V=UnitP V:= by
     have hz := (he 0 ⟨le_rfl,zero_le_one⟩ ∅); rw [zap M g H h,show P0 V 0 ∅=0 from ?_, Real.exp_zero,mul_one] at hz; exact hz
     simp only [Heron.bouquet, Ink.blanker,tsum_zero]
   exact ht ▸ ⟨hF V,he⟩

lemma press (h:grows M)(J:Config G c→Ways ι)(m:ℕ)(hm:Fintype.card ι ≤ m) (V:Config G c)
   (ha:0<UnitP V)(hT : ∀ t∈ Set.Icc (0:ℝ) 1,∀ x, UnitP V*Real.exp (J V t x)=S.push R.beta (Palette.buy M (Palette.ways g t x) S) V) (he : J V 0 ∅=0) (hW: Paid (fun _:Unit=> J V) d)(p:Finset ι): jet (J V) p= Slate.shell m (projection M g (S:=S) V) m p:= by
   have hU: jet (fun i p=> Real.exp (J V i p))= projection M g (S:=S) V:= funext fun k=> (congr_fun (Switch.cong (Switch.approached.mono (fun t hi=> funext fun x=> (show Real.exp _= S.push R.beta (Palette.buy M (Palette.ways g t x) S) V / UnitP V by rw [←hT t ⟨hi.1.le,hi.2⟩, mul_div_cancel_left₀ _ (ha.ne')])))) k).trans (in_record M g H h k V)
   rw [Slate.protocol hW he m hm m p ((card_le_univ p).trans hm),hU]
end Staircase
end YM.RGComparison01.Pledge
