import YM.RGComparison01.Marks.Canyon
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
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Checks
open Foreman Baked Palette Pillow Selector March Season
variable {M:ι→Leaf R} {ρ:ι→ℝ} {z: Cl M H}
-- full-priced RegBudget on support basis. distinguished λ weights specifically absorbed.
def Rooted {ι:Type} (H:ι→Support c)(f:ι → Config G c→ℝ)(P:BudgetPoint) (a w:ℝ) := ∃ u:ι→ℝ,(∀ i, P.Regular (H i) (f i) ∧ 0≤u i ∧ ∀ j∈H i,P.supBounds j (H i) (f i) (u i)) ∧ Ac.Hit H P.B u a w
variable (Z : Cl M H→Prop) (U:Knot Ω e B a t A D k)
   (P:BudgetPoint) (hp : P.threshold=Pressure.temp s)(hj : P.order≤j)(hk : P.power ≤ n)(hP : P.B = radiusB s)
def treat (S : Cl M H →Prop):=fun p:Cl M H=> if S p then glass M ρ χ p else (0:Config G _→ℝ)
include U hp hj hk hP
lemma rendered (hx:Casing R x Ψ) (hr: ∀ i,0≤ρ i) {h:Cl M H→ℝ} {f:ℝ} (he : Ac.Hit (origins M H) (radiusB s) (fun p=> h p * RegDebt M ρ p Ω k n B (maskRaise Ω Ψ x e)) c' w)
   (hf:0<f) (hg: ∀ p,Z p→ f ≤ h p) : Rooted (origins M H) (treat (χ:=χ) (ρ:=ρ) Z) P c' (w / f):= by
   let g p:= RegDebt M ρ p Ω k n B (maskRaise Ω Ψ x e); let L:=fun p=> if Z p then g p else 0
   have hh : ∀ p,0≤g p:=by
      intro p; have he:0 ≤ shiftG s:= by unfold shiftG; positivity
      exact mul_nonneg (pow_nonneg (mul_nonneg he (add_nonneg zero_le_one (by positivity : 0 ≤ ((coverNumber (radiusB s) (origins M H p)):ℝ)))) _) (grain M ρ Ω p U.paidB hx U.paidE hr)
   have hz p:0 ≤ L p:= by unfold L; split; exact hh p; rfl
   refine ⟨L,fun i=>?_,fun i=>?_⟩
   · unfold L treat; split
     next _=> exact ⟨(pride M ρ U hx hr i P hp hj hk).2.1,hh i,(pride M ρ U hx hr i P hp hj hk).2.2⟩
     next=> exact ⟨CouplingShape.reg_const _,le_rfl,fun x hx=> sup_le (CouplingShape.sup_const _) abs_zero.le⟩
   have h := budget_scale (inv_pos.mpr hf).le (he i); rw [div_eq_mul_inv, mul_comm w, hP]; refine budget_mono h (fun j=>?_) (fun j=>?_)
   · split; exact mul_nonneg (hz _) (Real.exp_nonneg _); rfl
   split
   next hi=>
      dsimp only; unfold L; split
      next ha=> rw [le_inv_mul_iff₀ hf,← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hg _ ha) (hh _)) (Real.exp_nonneg _)
      rw [zero_mul]; simpa only [hi, ↓reduceIte] using h.1 j
   next=> rw [mul_zero]

omit U hp hj hk hP
-- if budget at every positive strength cost arbitrarily small, pass at zero.
lemma at_zero {X : Type} {Y:X→Support c} {F:X→ Config G c→ℝ}
    (h: ∀ r:ℝ,0 < r→ Rooted Y F P a r) : Rooted Y F P a 0 := by
   obtain ⟨d,hd,hD⟩:= h _ zero_lt_one
   refine ⟨fun i=>0,fun i=> ⟨(hd i).1,le_rfl,fun j hj=> ?_⟩,fun i=> ?_⟩
   · refine ⟨le_rfl,fun V hv l hl hA=> ?_⟩
     apply le_of_forall_gt_imp_ge_of_dense; intro u hu
     let v:=Real.exp (a*coverNumber P.B (Y i)); have ht:0<v:= Real.exp_pos _
     obtain ⟨b,hb,hB⟩:= h _ (mul_pos hu ht)
     have hw : b i * v ≤ u*v:= by simpa only [hj,if_true] using budget_single (hB j) i -- possible cast diff
     exact ((hb i).2.2 j hj|>.2 V hv l hl hA).trans (le_of_mul_le_mul_right hw ht)
   simp [SumBudget]
lemma credited {X:Type} {Y:X→Support c} {F:X → Config G c→ℝ}(h:Rooted Y F P a w)(hx:w ≤ v): Rooted Y F P a v:= by obtain ⟨b,he,hP⟩:=h; exact ⟨b,he,fun i=>budget_loosen (hP i) hx⟩

variable {p₁ u m kk : ℕ} {b g h s' v : ℝ→ℝ} (B : BudgetPoint)

variable [Fintype ι] (hQ : Cellar Q χ W L S.patch o B.order k kk B.power μ a δ b g h s' v s) -- notation fix and k'
variable (hk:H = H)
include H hQ
lemma sellers {t:ℝ} (he : Bench M ρ (b s)) (hx : Stamp T) (hF : (Tithe.portion R.activities Ψ).EBound R.p t) (ht : t ≤ incomingE G L s)
    (hm: B.B=radiusB s) (hB:B.threshold= Pressure.temp s) (hw:Height.grow G L s^k ≤ Real.exp ((Q).mark L μ s)) :
    Rooted (origins M H) (fun p=> glass M ρ χ p) B a (h s) ∧
    Rooted (origins M H) (treat (χ:=χ) (ρ:=ρ) (fun i=> Season.Heavy kk i∧ ¬Ode Ψ i)) B a (h s/(Height.grow G L s^k)) ∧
    Rooted (origins M H) (treat (χ:=χ) (ρ:=ρ) (Ode Ψ)) B a (s' s*t) := by
   obtain ⟨q,j,n,Z,r,e,D,c,H',A',d,X,hΛ,hH⟩:= ((hQ.buys c f S T rfl hx R C H).2)
   have hr := (show ∀ i:ι,0≤ρ i from (Exists.elim he fun _ h=> h.2.1))
   let v:= Height.grow G L s; have hv:1 ≤ v:= hQ.life
   have hp: t≤ b s:= ht.trans (hQ.covers.trans (min_le_right ..))
   obtain ⟨F,hx',hf⟩:= hH _ M ρ he Ψ _ 1 hF ht le_rfl (by rwa [one_mul]) -- syntax H arg? 
   refine ⟨?_, rendered _ hΛ B hB le_rfl le_rfl hm hx' hr hf (show 0<v^k from pow_pos (zero_lt_one.trans_le hv) k) (fun p hp=> wealth le_rfl hQ.pole (one_le_pow₀ hv) hp.1 hp.2 hQ.sizes le_rfl hw hQ.long),?_⟩
   · have hh:= rendered (fun _=> True) hΛ B hB le_rfl le_rfl hm hx' hr hf zero_lt_one (fun z _=> safe le_rfl hQ.pole (one_le_pow₀ hv) z)
     unfold treat at hh; simp_rw [if_true,div_one] at hh; exact hh
   rcases eq_or_lt_of_le (show 0≤t from by obtain ⟨x,hb,hv⟩:=hF; exact budget_nonneg (hv 0)) with h₀|h₀
   · rw [← h₀,mul_zero]; apply at_zero B; intro x hx; have hz: ∀ᶠ y:ℝ in atTop, h s/y ≤ x:= by
         have he:= tendsto_const_nhds (x:=h s)|>.mul (tendsto_inv_atTop_zero (𝕜:=ℝ)); simp_rw [mul_zero] at he; simp_rw [div_eq_mul_inv]; exact (he.eventually (gt_mem_nhds hx)).mono fun i hi=>hi.le
     obtain ⟨w,hw,hV⟩:= (hz.and (eventually_ge_atTop 1)).exists
     obtain ⟨X,hX,hU⟩:= hH _ M ρ he Ψ _ w hF ht hV (by rw [← h₀,mul_zero]; exact hQ.crucial.le)
     exact credited B (rendered _ hΛ B hB le_rfl le_rfl hm hX hr hU (zero_lt_one.trans_le hV) (fun p h=> oasis hV hQ.pole (one_le_pow₀ hv) h)) hw
   let x:= b s / t; have he' : 1 ≤ x:= (one_le_div h₀).2 hp; obtain ⟨X,hX,hU⟩:= hH _ M ρ he Ψ _ x hF ht he' (div_mul_cancel₀ _ h₀.ne'|>.le)
   rw [← hQ.spelled]; refine credited B (rendered _ hΛ B hB le_rfl le_rfl hm hX hr hU (zero_lt_one.trans_le he') (fun p h=> oasis he' hQ.pole (one_le_pow₀ hv) h)) ?_
   apply le_of_eq; unfold x; rw [← div_eq_mul_inv, div_div_eq_mul_div]; ring
end Checks
end YM.RGComparison01.Pledge
