import YM.RGLocalTaylor.Retain.Vital
/-!
# Log-Exponent L←E projection, full mask and event supports.

For replacing inherited kernels use same `regFoot` ALWAYS. Estimate even for
arbitrary unknown incoming E error: at most staged iteration size. The `Bond`
unit-vacant Lens not altered by fitting an alternate catalogue. All tickets
on the post norm of the true histories for actual Z.Geometry, before
attaching new E. No making a valid alternate post-B answer from evaluation.
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


open Post PhysicalNext PhysicalNext.Repeat
open Blaze.March Captain
namespace Retain

local notation "E!" => Opacity.key S

-- canonic grammar computes this on supplied predictive E in the same address chart.
def mage (_H: Cash W s μ L Q o C T R)(p: glyph G f)(i:ℕ) : Insert T:=
  { value:=fun {_} X z=> let u:= worldZ X R.beta z;
                          - (imprint R.activities p).regularOccurrence R.p i (X.input u)* X.enforce (2*o.a) u (X.plaza (Raw.space T 0 X.B R (.inl i))) }

private lemma mAdd (p w:glyph G f)(X:Coat T F)(i:ℕ)(z:Air f G): (mage H (p+w) i).value X z=(mage H p i).value X z+(mage H w i).value X z:= by
  let u:=worldZ X R.beta z; let t:= R.p.threshold; let U:= X.input u; let S:=(R.activities.reg i).support
  unfold mage Activities.regularOccurrence imprint; dsimp only [Pi.add_apply]; by_cases ht:Healthy t S U <;> dsimp only [t,S,U,u] at ht; simp only [masked_eq _ _ _ _ ht,Pi.add_apply]; ring; simp only [masked_ne _ _ _ _ ht,neg_zero,zero_mul,add_zero]

def shelved (_H: Cash W s μ L Q o C T R)(w:ℕ→ℝ):Prop:=
    (∀ i,w i ≤ 1/8) ∧ ∀ i V, ‖R.activities.regularOccurrence R.p i V‖≤w i
local notation "E₀" => R.activities.E
private lemma mScale (p:glyph G f)(X:Coat T F)(a:ℝ)(i:ℕ)(z:Air f G): (mage H (a•p) i).value X z=a*(mage H p i).value X z:= by
  unfold mage Activities.regularOccurrence imprint; dsimp only [Pi.smul_apply,smul_eq_mul]; by_cases ht:Healthy R.p.threshold (R.activities.reg i).support (X.input (worldZ X R.beta z)); simp only [masked_eq _ _ _ _ ht,Pi.smul_apply,smul_eq_mul]; ring; simp only [masked_ne _ _ _ _ ht,neg_zero,zero_mul,mul_zero]

lemma realizor (i:ℕ) (V:Finset ℕ)(X:Coat T F)(z:Air f G) : (leg H V (E! i)).value X z=Real.exp ((mage H E₀ i).value X z)-1:= rfl

variable (w' : ℕ→ℝ) (hw : shelved H w')(i:ℕ)
include hw
lemma effect (X: Coat T F)(z:Air f G) : ‖(mage H E₀ i).value X z‖ ≤ w' i:=by
  unfold mage; dsimp only; rw [norm_mul,norm_neg]; refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) (hw.2 ..); rw [Real.norm_of_nonneg (X.conserve ..|>.1)]; exact X.conserve ..|>.2
lemma keepsLog (X:Coat T F)(z:Air f G)(V: Finset ℕ): |(leg H V (E! i)).value X z| ≤ 1/4:= by
  rw [realizor]; exact (Real.abs_exp_sub_one_le ((effect w' hw i X z).trans ((hw.1 i).trans (by norm_num)))).trans (by exact (mul_le_mul_of_nonneg_left ((effect w' hw i X z).trans (hw.1 i)) zero_le_two).trans (by norm_num))
lemma fits_mage : Fits H (mage H E₀ i) (H.supportP (E! i)) j := by
  rw [show mage H E₀ i= (leg H ∅ (E! i)|>.mapSmooth Mayer.recoverLog) from ?_]; exact Fits.mapSmooth (fits_leg H ∅ (E! i) j) (Mayer.log_smooth j)
  change Insert.mk _=Insert.mk _; congr! 1; funext F X z; exact Eq.symm ((by rw [realizor]; exact Mayer.recovers _ (realizor i ∅ X z ▸ keepsLog w' hw i X z ∅): Mayer.recoverLog ((leg H ∅ (E! i)).value X z)=(mage H E₀ i).value X z))
lemma m_payload (V : Finset ℕ) (t : Fin n) : Mayer.kernelQuote H V t.castSucc (E! i)= (mage H E₀ i).mapSmooth (fun x=>x^(t.val+1)/(t.val+1).factorial) := by
  change Insert.mk _=Insert.mk _; congr! 1; funext F X z; rw [realizor]; exact Mayer.index_interior _ _ ((realizor i V X z) ▸ (keepsLog w' hw i X z V))
omit hw
variable {p:glyph G f}
variable {Ξ:Utopia H j v d r C' χ} {d' e uJ vJ:ℝ}
lemma mStamp (h : Awning H Ξ A b d' e uJ vJ k l)(hp : ∀ V, ‖(imprint R.activities p).regularOccurrence R.p i V‖ ≤ w' i)(hP:R.p.Regular (R.activities.reg i).support (p i)): EstFactor Ξ (E! i) (mage H p i) A (w' i) vJ := by
  intro F X z hX hK hχ hM hh E _ _ _ V x hy hv
  let f t := steer X A (worldZ X R.beta z) (V t); let t:=(2*o.a)
  let p₀ := Raw.space T 0 X.B R (.inl i);  let w:= worldZ X R.beta z
  let n :ℝ:=-(imprint R.activities p).regularOccurrence R.p i (X.input w)
  let q t:=n*X.enforce (2*o.a) (f t) (X.plaza p₀)
  have hQ:=(h.course_prices F X z hX hK hχ hM E V x hy hv); have hr := hQ.1
  have hE : (fun i'=> (mage H p i).value (vary X (V i')) (course X A R.beta z (V i')))=ᶠ[𝓝 x] q:=by
     filter_upwards [hr.patch] with u hu
     unfold mage q n; dsimp only; rw [hr.moving u]; let X':= vary X (V u); by_cases ht: X'.enforce (2*o.a) (f u) (X'.plaza p₀)=0; change _*X'.enforce (2*o.a) (f u) (X'.plaza p₀)=_*X'.enforce (2*o.a) (f u) (X'.plaza p₀); rw [ht,mul_zero,mul_zero]; refine congr_arg₂ (· * ·) (congr_arg Neg.neg ?_) rfl; exact valueE {R with activities:=imprint R.activities p} i hP _ _ ((plastic hu hr.pulse).venial _ ht)
  have ht : z∈ X.catastrophe (o.ξ/2) R.beta (blaze ({E! i}: Molecule S)):= by
     suffices h : (blaze ({E! i}: Molecule S))=∅ from h.symm ▸ (fun k (h:k∈(∅: Finset (WarningAt c _)))=> (Finset.notMem_empty k h).elim) -- edit
     ext; simp [blaze,Opacity.key]
  rw [Set.indicator_of_mem ht]; apply Brush.shimmy _ hE
  have hh':p₀⊆H.supportP (E! i):=by
    have hx:X.B=radiusB s:=congr_arg radiusB hX; unfold p₀; rw [hx]; exact (Corona.halo_mono (by simp) (Finset.Subset.refl _))
  refine ((hQ.2.2 p₀ _ hh').smul n).climb ?_ ?_
  · rw [mul_one]; unfold n w; rw [norm_neg]; apply hp
  apply mul_le_mul_of_nonneg_left _ h.cSc; change (coverNumber X.B (H.supportP _) :ℝ) ≤ 1+(_+ ↑(_ :ℕ)); rw [show X.B=radiusB s from congr_arg radiusB hX]; exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one)
-- more budget next
end Retain
end YM.RGLocalTaylor
