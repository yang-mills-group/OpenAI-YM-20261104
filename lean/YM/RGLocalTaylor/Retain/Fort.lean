import YM.RGLocalTaylor.Retain.Stencil
/-!
# Inherited E damage along the ACTUAL one-step stencil

Scale witness normalized **only for estimation** at stage capacity A.clock.
Trial impulse retains exactly the same label positions, Cohesion & Gauge.
Pay protected mask on all occurrences. Supplies *effective-exp* predicted
kernel entries when given prior estimate of incoming E in same support API.
No actual branch changes. No WarmCurve ownership granted to subsidiary data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open Mayer goodK Post
namespace Fort

variable (H)
def mantle (f₁ : glyph G f)(M:ℕ) : Stencils T M := fun Y p i=> Function.extend (Opacity.key S)
    (fun i=> (mage H f₁ i).mapSmooth (fun x=>x^(p.val+1)/(p.val+1).factorial)) (fun i=> physical H M Y p i) i
variable {M i :ℕ} {f₁ f₂ : glyph G f} {X : Cash W s μ L Q o C T (impulse R f₂ a)}

local notation "κ" => Opacity.key S
local notation "χ!" => impulse R f₂ a
local notation "Ru" => R.activities.E
set_option quotPrecheck false
local notation "V'" => (χ!).activities.E
local notation "RuM" => mantle H f₁ M
local notation "U!" => physical H M
lemma lifts (S:StepData c f): Function.Injective (Opacity.key S):= by intro i j h; simpa [Opacity.key] using h
lemma other (t : ℕ)(i:Finset ℕ)(p:Fin (M+1)) : RuM i p (κ t)= (mage H f₁ t).mapSmooth (fun x=>x^(p.val+1)/(p.val+1).factorial):= (lifts _).extend_apply _ _ t
lemma keepsOff (f₁:glyph G f) {q:Head S} (p:Fin (M+1))(V:Finset ℕ)(h:q∉ Set.range (Opacity.key S)) : mantle H f₁ M V p q=physical H M V p q:= extend_apply' _ _ _ h
lemma shell {V:Head S}: (V∈Set.range (Opacity.key S)) → Exponential V:=by rintro ⟨v,rfl⟩; exact ⟨Sum.inl (Sum.inl v),rfl⟩ -- remove q

-- these are generalized (Inherits proof made private originally).
lemma add_m (g t:glyph G f) (b:ℕ) : mage H (g+t) b= (mage H g b).sumTwo (mage H t b):=by
   change Insert.mk _=Insert.mk _; congr! 1; funext F X z
   let U:= X.input (worldZ X R.beta z); let S:=(R.activities.reg b).support
   unfold mage Activities.regularOccurrence imprint; dsimp only [Pi.add_apply]; by_cases ht:Healthy R.p.threshold S U <;> dsimp only [S,U] at ht; simp only [masked_eq _ _ _ _ ht,Pi.add_apply]; ring; simp only [masked_ne _ _ _ _ ht,neg_zero,zero_mul,add_zero]
lemma sub_m (g t:glyph G f)(b:ℕ) : mage H (g-t) b= (mage H g b).difference (mage H t b):=by
   have ht : (mage H (g-t) b).sumTwo (mage H t b)=mage H g b:= by rw [←add_m, sub_add_cancel]
   change Insert.mk _=Insert.mk _; congr! 1; funext F X z; change (mage H (g-t) b).value X z=(Insert.difference _ _).value X z -- perhaps fails placeholder
   rw [Insert.gap, ← ht,Insert.sumTwo]; dsimp only; ring
lemma scaled (g:glyph G f)(a:ℝ)(i:ℕ): mage H (a•g) i=(mage H g i).shrink a:=by
   change Insert.mk _=Insert.mk _; congr! 1; funext F X z
   unfold mage Activities.regularOccurrence imprint; dsimp only [Pi.smul_apply,smul_eq_mul]; by_cases ht : Healthy R.p.threshold (R.activities.reg i).support (X.input (worldZ X R.beta z)); simp only [masked_eq _ _ _ _ ht,Pi.smul_apply,smul_eq_mul]; ring; simp only [masked_ne _ _ _ _ ht,neg_zero,zero_mul,mul_zero]
lemma boost_lowers (g:glyph G f)(a:ℝ)(ha:a≠0)(i:ℕ): mage H g i=(mage H (a⁻¹ • g) i).shrink a:=by rw [← scaled, smul_smul,mul_inv_cancel₀ ha,one_smul]

variable (i)
variable {e vJ uJ K θ α ώ β Z r':ℝ}
   {Ξ : Utopia H j v d r C' χ}
   {N : Captain H j C' d v Y A b r B q n χ}

lemma arranged (V:Head S)(h:Exponential V): Ξ.tag V=Ξ.fare V:=by
   have hh:= Ξ.remixes ({V}:Molecule S); rw [noBlaze h,Finset.card_empty, pow_zero] at hh; simpa only [prod_singleton, mul_one] using! hh.symm

lemma relay {f':Insert T}{S:Support c} (hw : Fits X f' S j): Fits H f' S j := ⟨fun F G hX h Y z z' ht hV=> hw.regional F G hX h Y z z' ht ⟨hV.toVillage,hV.airs,fun _ _=>Iff.rfl⟩, hw.along,hw.onGauge,hw.near ⟩

-- Affine cap covers from actual & trial.
structure dual (H: Cash W s μ L Q o C T R) (f₂:glyph G f) (a:ℝ)(p p':ℕ→ℝ) : Prop where
    size : shelved H p
    bill : ∃ X:Cash W s μ L Q o C T (impulse R f₂ a), shelved X p'
    pos : 0 < a
    modest : a ≤ 1

variable {d' : ℝ}{w w':ℕ→ℝ}
    (hh : dual H f₂ a w w') (ha:Awning H Ξ A b d' e uJ vJ k l)
include hh
lemma force_m : Fits H (mage H f₂ i) (H.supportP (κ i)) j:=by
   obtain ⟨X,hX⟩:= hh.bill; rw [boost_lowers H _ _ hh.pos.ne' i]; apply Fits.shrinkFits; apply relay H (X:=X); exact fits_mage w' hX i
lemma mnonneg : 0≤w i ∧ 0≤w' i:= by obtain ⟨X,hX⟩:= hh.bill; exact ⟨le_trans (norm_nonneg _) (hh.size.2 i (1:Config G f)), le_trans (norm_nonneg _) (hX.2 i (1:Config G f))⟩
omit hh in
lemma always (p:Head S)(he: Exponential p) (V: Coat T F) (z:Air f G): z∈ V.catastrophe (o.ξ/2) R.beta (blaze ({p}:Molecule S)):=by rw [noBlaze he]; exact fun i hi=>False.elim (notMem_empty i hi)
omit hh in
lemma warm (V:Coat T F)(z: Air f G): z∈ V.catastrophe (o.ξ/2) R.beta (blaze ({κ i}:Molecule S)):= always (κ i) (shell (Set.mem_range_self _)) V z -- he q cleanup
include ha
lemma spatial : EstFactor Ξ (κ i) (mage H f₂ i) A (a*w' i) vJ:=by
   obtain ⟨X,hX⟩:=hh.bill; rw [boost_lowers H _ _ hh.pos.ne']
   have ht := mStamp (p:=(impulse R f₂ a).activities.E) w' i (h:=ha) (H:=H) (hp:=hX.2 i) (hP:= X.laws.intake.cap.labels.regular.smooth i)
   intro F X z s' hK hχ hM hH E _ _ _ V x he hv; have hh:= ht F X z s' hK hχ hM hH E V x he hv; rw [Set.indicator_of_mem (warm (o:=o) (R:=R) i X z)] at hh ⊢ -- args
   simpa only [Real.norm_of_nonneg ‹dual ..›.pos.le] using! hh.smul a
lemma birth : EstFactor Ξ (κ i) (mage H Ru i) A (w i) vJ:= mStamp (H:=H) w i ha (hh.size.2 i) (H.laws.intake.cap.labels.regular.smooth i)

variable (hw : R.activities.E=f₁+f₂)
local notation "w₀" => w i + w' i
omit ha
include hw
lemma insulation : Fits H (mage H f₁ i) (H.supportP (κ i)) j:= by rw [show f₁=Ru-f₂ by rw [hw,add_sub_cancel_right], sub_m]; exact Fits.diffFits (fits_mage w hh.size i) (force_m H i hh)
include ha
lemma budget : EstFactor Ξ (κ i) (mage H f₁ i) A (w₀) vJ:=by
   have he : f₁=Ru-f₂:= by rw [hw, add_sub_cancel_right ]
   rw [he, sub_m]; intro F X z s' hK hχ hM hH E _ _ _ V x hf hv; have hb:= birth H i hh ha F X z s' hK hχ hM hH E V x hf hv; have h:= spatial H i hh ha F X z s' hK hχ hM hH E V x hf hv
   rw [Set.indicator_of_mem (warm (o:=o) (R:=R) i X z)] at h hb ⊢; simp_rw [Insert.gap]; exact (hb.separating h).climb (add_le_add_right (mul_le_of_le_one_left (mnonneg H i hh).2 hh.modest) _) le_rfl -- add_right? inspect
end Fort
end Retain
end YM.RGLocalTaylor
