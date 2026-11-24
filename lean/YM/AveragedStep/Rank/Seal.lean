import YM.AveragedStep.Rank.Compare
/-! Uniform all period inverse bill at the integrated SD equation;
no Harmonic assumption at infinity. No assertion on the standard physical
field Gram horizon (or the weighted analytic widths in an E/K trajectory).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
open Progress.StationaryScenes.Green
variable {c f: Side}{G:Gauge}{S:StepData c f} (F:Forest S.ratio)

def start (i:Key F G):Site f:=i.1.val.1
def keyMask (G:Gauge):ℕ:=4*Fintype.card G.ColorIndex
lemma start_card : Multiplicity (start (G:=G) F) (keyMask G):=by
 have h:=multiplicity_by (start (G:=G) F) (fun i => (i.1.val.2,i.2)) ?_
 · simpa only [Fintype.card_prod, Fintype.card_fin,keyMask] using! h
 rintro ⟨⟨⟨x,i⟩,hx⟩,j⟩ ⟨⟨⟨y,r⟩,hy⟩,p⟩ e
 simpa only [start,Prod.mk.injEq,Subtype.mk.injEq,and_assoc] using e
variable (h:S.patch.Branches S.kernel G)
include h
lemma absent (A:ChartRatio G)(i j:Key F G)(e: (Sum.inl j.1.val:Rim c f) ∉ home S (.inl i.1.val)):body A F i j=0:=by
 unfold body; rw [of_apply,tier, if_pos rfl,sub_zero]; apply Finset.sum_eq_zero
 intro p hp; rw [tooths h, back_take]
 have he:p∉owners S (Sum.inl j.1.val):= fun hc=> e (home_owner S hp (own_need S hc))
 rw [pick_zero p he,map_zero];rfl
lemma balanced (t:S.Choices)(A:ChartRatio G): (body A F).IsHermitian:=by
 have hp r : ContDiffAt ℝ ω (Function.uncurry (tested (S:=S) F r firstClip (wil G))) 0 :=
    (price_identity F r (initial_bounds G zero_lt_one le_rfl (show (0:ℝ)≤0 from le_rfl) rfl) h).1
 have he : IsHermitian (hessian F t firstClip (wil G) 0 0):= Progress.StationaryScenes.Green.symmetric t hp
 rw [identified h t];
 ext i j; simp only [conjTranspose_apply,transpose_apply,star_trivial]; exact (show _= _ from congrFun (congrFun he j) i) -- direction

omit F h in
private lemma ceilingFor (P:Patch)(K:KernelChoices)(A:ChartRatio G):∃ B:ℝ,0≤B∧∀{c f:Side} (S: StepData c f)(F:Forest S.ratio), S.kernel=K→ S.patch=P → ∀ i j,|body A F i j|≤ B:=by
 choose B hb h using (fun i:G.ColorIndex=>tier_cost P K A (fingers G i) 0)
 refine ⟨∑ i,B i,Finset.sum_nonneg fun i _=>hb i,fun {c f} S F he hu i j=>?_⟩
 apply le_trans ?_ (Finset.single_le_sum (fun i _=>hb i) (Finset.mem_univ i.2))
 unfold body; rw [of_apply]; have ht:=h i.2 S he hu (Sum.inl i.1.val) (back F (frame F j)) (r:=1) le_rfl ?_
 · simpa only [one_pow,mul_one] using ht
 rw [back_take]; intro k hk; by_cases he:k=Sum.inl j.1.val; subst he; simp [fingers]
 rw [Pi.single_eq_of_ne he]; simp

structure Wage (G:Gauge) (P:Patch)(K:KernelChoices)(A:ChartRatio G) where
    η:ℝ
    μ:ℝ
    available:0<η
    active:0<μ
    lawful{c f:Side}(S:StepData c f)(F:Forest S.ratio): S.kernel=K→ S.patch=P →
      Bid.Larger (G:=G) S → IsUnit (body A F).det ∧ Sealed (start F) η (body A F)⁻¹ μ

omit F h in
lemma activated (G:Gauge) (P:Patch)(K:KernelChoices)(A:ChartRatio G) : Nonempty (Wage G P K A) :=by
 obtain ⟨C,D,hH⟩:=link_charge G P.J K
 obtain ⟨B,hB,H⟩:= ceilingFor (G:=G) P K A
 let L:=zeroGap P K firstClip C D
 have hL:0<L:= zeroGap_pos ..
 let M:=B*Real.exp (1*(2*aperture P:ℝ)); have hM:0≤M:=by unfold M; positivity
 let α:=tiltWidth (keyMask G) L 1 M
 refine ⟨α,(L/2)⁻¹,tiltWidth_pos _ hL zero_lt_one hM,by positivity,?_⟩
 intro c f S F hk hP hp
 have hw : Sealed (start F) 1 (body A F) M:=by
   intro i j; by_cases he: (Sum.inl j.1.val:Rim c f) ∈ home S (Sum.inl i.1.val)
   · unfold M Decay
     rw [mul_assoc,← Real.exp_add]
     have ht:=reach_home S (Sum.inl i.1.val) he
     refine (H S F hk hP i j).trans (le_mul_of_one_le_right hB (Real.one_le_exp ?_))
     rw [one_mul,neg_mul,one_mul, ← hP]; apply sub_nonneg.mpr
     exact_mod_cast ht
   rw [absent F hp.1 A _ _ he,abs_zero]; exact mul_nonneg hM (decay_pos ..).le
 have hh:Harness G S.patch.J S.kernel C D:=by rw [hk,hP]; exact hH
 let t : S.Choices:= Classical.arbitrary _
 have h1: S.patch.Branches S.kernel G:=hp.1
 have hf : PriceGap F firstClip (wil G) L:=by
    unfold L; rw [← hP,← hk]; exact symbolic_gap F (initial_bounds G zero_lt_one le_rfl (show (0:ℝ)≤0 from le_rfl) rfl) hp hh
 have hv:=counted t hf
 have hg : IsHermitian (body A F):=balanced F h1 t A
 have he: Charge (body A F) L:=by
    intro X
    unfold IsHermitian at hg
    simp_rw [pow_two]
    -- use counted transposed identity & symmetry
    change L*dotProduct X X ≤ _
    have hm:=identified h1 t F A
    have hx:(body A F)ᵀ=hessian F t firstClip (wil G) 0 0:= by rw [hm,transpose_transpose]
    apply (hv X).trans_eq
    have hs:(body A F)ᵀ=body A F:=by ext i j; exact congrFun (congrFun hg i) j
    rw [← hx,hs]
 have hdet:IsUnit (body A F).det:= isUnit_iff_ne_zero.mpr (he.positive hg hL).det_pos.ne'
 exact ⟨hdet,inverse_sealed hw hL zero_lt_one he hM (start_card F) hdet⟩
end YM.AveragedStep
