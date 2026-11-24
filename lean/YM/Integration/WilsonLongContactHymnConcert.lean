import YM.Integration.WilsonLongContactHymnMeasure
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Crowd

/-! Bound the derivatives of a fully occupied support after the same normalized
Gaussian integral, retaining its original rate in every rooted angular direction. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactHymn
open PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad PhysicalNext
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff Push.SectorMeasure Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
open PhysicalNext.JointLoad.Heir.Lute
lemma decay_pos {L : Side} : 0 < decay B L X := by unfold decay; split <;> positivity
private lemma raisePrice (n : ℕ) {a b s : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) : (a+b*s^2)^(n+n) ≤ (a+a)^(n+n)*(1+b^(n+n)*s^(2*(n+n))) := by
  let d := n+n
  have hp : 0≤b*s^2 := mul_nonneg hb (sq_nonneg _)
  rw [pow_mul, ← mul_pow]; rcases le_or_gt (b*s^2) 1 with h|h
  · exact (pow_le_pow_left₀ (by positivity) (add_le_add_right (h.trans ha) a) d).trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg hp _)))
  rw [mul_add,mul_one,← mul_pow]; apply le_add_of_nonneg_left' (pow_le_pow_left₀ (by positivity) _ _) (by positivity : 0 ≤ (a+a)^d)
  rw [add_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) h.le) (le_mul_of_one_le_left hp ha)
where le_add_of_nonneg_left' {u v w : ℝ} (h : u≤v) (he : 0≤w) : u≤w+v := h.trans (le_add_of_nonneg_left he)


theorem restored (B : BudgetPoint) (L : Side) (X : Support f) :
    1 ≤ (L.val:ℝ)^5 * decay B L X := by
  have hl : 0<(L.val:ℝ) := Nat.cast_pos.mpr L.property
  have hL : 1≤(L.val:ℝ) := by exact_mod_cast L.property
  unfold decay
  split
  · rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hl.ne')]
  · simpa using one_le_pow₀ (n:=5) hL

omit [DecidableEq ι] in
theorem fare (C : Libretto G n) (D : Record) (P B : BudgetPoint) (L : Side)
    (X : Support f) (r : ℕ) (x u : ℝ) (hu : 0≤u) (z : Prices G ι) :
    grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n ≤
      (L.val:ℝ)^5 * (phrase C * decay B L X) *
        (leading C + rust C D P B L X r x u * powers z^2)^n := by
  have hA := ample_one n X P B D.majorant C.matins C.C_one (x:=x)
  have hL := leading_one C
  have hF := patterns_nonneg n
  have hR := C.rights.large
  have hs := one_le_pow₀ (n:=2) (grows z)
  have hb : 0 ≤ rust C D P B L X r x u := rust_nn hu
  have hseg : segment n X P B D.Q C.M (loom P (reach x) C.C) ≤
      rust C D P B L X r x u * powers z^2 :=
    le_trans (b:=rust C D P B L X r x u)
      ((le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans D.majorant) hu B.threshold_pos.le)).trans
       (le_add_of_nonneg_right (scratch_nn n))) (le_mul_of_one_le_right hb hs)
  have h₁ : grandFee C.rights ≤ (L.val:ℝ)^5 * (phrase C * decay B L X) := by
    calc
      _ ≤ phrase C := by unfold phrase shortFee; apply le_add_of_nonneg_left; positivity
      _ ≤ _ := by rw [mul_left_comm]; exact le_mul_of_one_le_right (phrase_nn C) (restored B L X)
  have h₂ : ample n X P B D.Q C.M C.C x ≤ leading C + rust C D P B L X r x u * powers z^2 := by
    unfold leading ample
    apply add_le_add _ hseg
    exact le_add_of_nonneg_left (by positivity)
  apply mul_le_mul h₁ (pow_le_pow_left₀ (zero_le_one.trans hA) h₂ n) (pow_nonneg (zero_le_one.trans hA) _)
  exact mul_nonneg (by positivity) (mul_nonneg (phrase_nn C) (decay_pos (B:=B) (L:=L) (X:=X)).le)

variable {Γ : Prices G ι → ℝ} (a : Museum F x A X Y ι) (he : Plays C D P B Pt T x) (origin : o∈X) (regular : B.Regular X f') (hτ : B.supBounds o X f' τ)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ)
include he origin regular hτ hY hu hΓ
theorem concert (U : Config G f) (hV : Healthy P.threshold Y V) (l : List (Directions G c)) (hl : l.length ≤ n) (ha : ∀ A∈l, P.dirBound (S.ratio.parent o) A) (z : Prices G ι) :
    let ρ := rust C D P B S.patch.L X r x u
    ‖leftDerivs (a.concert T u q d k f' Γ U V z) l V‖ ≤ (beat C*((S.patch.L.val:ℝ)^5*τ)*decay B S.patch.L X) * (1+ρ^(n+n)*powers z^(2*(n+n))) := by
  intro ρ; have ht := hτ.1
  obtain h := choir_band (k:=k) (q:=q) (d:=d) a U he origin regular hτ hY hu hΓ hV z
  have hw : 0 ≤ ρ := rust_nn hu; have hc := leading_one C
  let t := leading C+ρ*powers z^2; let p := phrase C; let D' := decay B S.patch.L X
  have h1 : 1 ≤ t := hc.trans (le_add_of_nonneg_right (mul_nonneg hw (sq_nonneg _))); have hp : 0 ≤ p := phrase_nn C; have hd : 0 ≤ D' := decay_pos.le
  calc
    _ ≤ (S.patch.L.val:ℝ)^5 * (p * D') * t^n * τ * t^n := (h.caps l hl ha).trans (mul_le_mul (mul_le_mul_of_nonneg_right (fare C D P B S.patch.L X r x u hu z) ht)
      ((pow_le_pow_left₀ h.sane (speed_le a hY origin hu z) _).trans (pow_le_pow_right₀ h1 hl)) (pow_nonneg h.sane _) (by positivity))
    _ = ((S.patch.L.val:ℝ)^5*(p*D')*τ)*t^(n+n) := by rw [pow_add]; ring
    _ ≤ ((S.patch.L.val:ℝ)^5*(p*D')*τ)*((leading C+leading C)^(n+n)*(1+ρ^(n+n)*powers z^(2*(n+n)))) := mul_le_mul_of_nonneg_left (raisePrice n hc hw) (by positivity)
    _ = _ := by unfold D' beat p; ring


omit he origin regular hτ hY hu hΓ in
theorem held (a : Museum F x A X Y ι) (he : Plays C D P B Pt T x)
    (origin : o∈X) (regular : B.Regular X f') (hτ : B.supBounds o X f' τ)
    (hY : Walled S X Y x r) (hu : 0≤u) {Γ : Prices G ι→ℝ}
    (hΓ : Silences G ι n u (D.ε*B.threshold) Γ) (U : Config G f) :
    P.supBounds (S.ratio.parent o) Y (a.hymn T u q d k f' Γ U)
      (((S.patch.L.val:ℝ)^5 * τ)*returnFee C D P B S.patch.L X r x u) := by
  let signed := fun V => a.concert T u q d k f' Γ U V
  let target := a.hymn T u q d k f' Γ U
  have measured (V : Config G c) (hV : Healthy P.threshold Y V) (l : List (Directions G c))
      (hl : l.length ≤ n) (_ : ∀ξ∈l,P.dirBound (S.ratio.parent o) ξ) :
      let g := fun z => leftDerivs (signed V z) l V
      let μ := Gaussian.cloud (a.twilight k T V)
      Integrable g μ ∧ ((leftDerivs target l V:ℝ):ℂ)=∫z,g z ∂μ :=
    (exchange a U he origin regular hτ hY hu hΓ hV l hl (k:=k) (q:=q) (d:=d)).2
  exact hall_general a he hY hu (mul_nonneg (by positivity) hτ.1) origin measured
    (fun _ hV l hl hA z => concert a he origin regular hτ hY hu hΓ U hV l hl hA z)

end YM.Integration.WilsonLongContactHymn
