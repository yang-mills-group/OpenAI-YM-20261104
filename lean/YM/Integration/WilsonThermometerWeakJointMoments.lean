import YM.Next.UV_STRESS.Station

/-! Signed smooth joint test profiles with unit integral and every prescribed
homogeneous moment zero, at the actual dimension of the near configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakJointMoments
open Set Filter MeasureTheory Spec Function Next.UVStress
open scoped Classical BigOperators Topology ContDiff
variable {n:ℕ}
def mass (f:Test n):ℂ:=f.applyTo (fun _=>1)
def Moments (f:Test n) (H:ℕ):Prop:=∀k,0<k→k≤H→∀A:ContinuousMultilinearMap ℝ (fun _ : Fin k=>Points n) ℂ,
  f.applyTo (fun x=>A (fun _=>x))=0

private theorem constant (f:Test n) (a:ℂ)(Z:Points n→ℂ):
    f.applyTo (fun x=>a*Z x)=a*f.applyTo Z:=by
  unfold Test.applyTo
  simp_rw [mul_left_comm (f _) a]
  exact integral_const_mul _ _

theorem scalar (f : Test n) (a : ℂ) (Z : Points n → ℂ) :
    (a • f).applyTo Z = a*f.applyTo Z := by
  unfold Test.applyTo
  change (∫ x, (a*f x)*Z x) = _
  simp_rw [mul_assoc]
  exact integral_const_mul a _

theorem difference (f g : Test n) (Z : Points n → ℂ) (hZ : Continuous Z) :
    (f-g).applyTo Z = f.applyTo Z-g.applyTo Z := by
  unfold Test.applyTo
  change (∫ x, (f x-g x)*Z x) = _
  simp_rw [sub_mul]
  exact integral_sub (f.smearing hZ.continuousOn) (g.smearing hZ.continuousOn)

def remove (j : ℕ) (f : Test n) : Test n :=
  ((2:ℂ)^j-1)⁻¹ • ((2:ℂ)^j • f - Next.UVStress.dilate (by norm_num : 0 < (2:ℝ)) f)

theorem remove_apply (j k : ℕ) (f : Test n) (Z : Points n → ℂ) (hZ : Continuous Z)
    (hscale : ∀ x, Z ((2:ℝ) • x) = (2:ℂ)^k*Z x) :
    (remove j f).applyTo Z = ((2:ℂ)^j-2^k)/(2^j-1)*f.applyTo Z := by
  rw [remove,scalar,difference _ _ _ hZ,scalar,Next.UVStress.zoom_integral,
    show (fun x => Z ((2:ℝ) • x)) = (fun x => (2:ℂ)^k*Z x) from funext hscale,
    constant]
  ring

theorem remove_mass {j : ℕ} (hj : 0 < j) (f : Test n) : mass (remove j f) = mass f := by
  have h : (2:ℂ)^j-1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (one_lt_pow₀ (by norm_num : (1:ℝ) < 2) hj.ne').ne')
  unfold mass
  rw [remove_apply j 0 _ _ continuous_const (fun _ => by simp),pow_zero,div_self h,one_mul]

theorem remove_moment (j k : ℕ) (f : Test n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Points n) ℂ) :
    (remove j f).applyTo (fun x => A (fun _ => x)) =
      ((2:ℂ)^j-2^k)/(2^j-1)*f.applyTo (fun x => A (fun _ => x)) := by
  apply remove_apply j k _ _ (A.cont.comp (continuous_pi fun _ => continuous_id))
  intro x
  change A (fun _ => (2:ℝ) • x) = (2:ℂ)^k*A (fun _ => x)
  rw [A.map_smul_univ (fun _ => (2:ℝ)) (fun _ => x)]
  simp [Complex.real_smul]

def prepare : ℕ → Test n → Test n
  | 0, f => f
  | j+1, f => remove (j+1) (prepare j f)

theorem prepared (H : ℕ) (f : Test n) : mass (prepare H f) = mass f ∧ Moments (prepare H f) H := by
  induction H with
  | zero => exact ⟨rfl, fun _ hk hh => by omega⟩
  | succ j ih =>
    refine ⟨(remove_mass (Nat.succ_pos j) _).trans ih.1,?_⟩
    intro k hk hkj A
    change (remove (j+1) (prepare j f)).applyTo _ = 0
    rw [remove_moment]
    by_cases he : k = j+1
    · simp [he]
    · rw [ih.2 k hk (by omega) A,mul_zero]

theorem unit_mass {x : Points n} (hx : x∈conf n) : ∃ f : Test n, mass f = 1 := by
  have h : ∃ f : Test n, mass f ≠ 0 := by
    by_contra! hz
    have hzero := (Test.weak_null (n := n) (K := fun _ => (1:ℂ)) continuousOn_const).mp hz
      hx
    exact one_ne_zero hzero
  obtain ⟨f,hf⟩ := h
  refine ⟨(mass f)⁻¹ • f,?_⟩
  change ((mass f)⁻¹ • f).applyTo (fun _ => (1:ℂ)) = 1
  rw [scalar,← mass,inv_mul_cancel₀ hf]


theorem original (H:ℕ){x:Points n}(hx:x∈conf n):∃f:Test n,mass f=1 ∧ Moments f H:=by
  obtain ⟨f,one⟩:=unit_mass hx
  exact ⟨prepare H f,(prepared H f).1.trans one,(prepared H f).2⟩

end YM.Integration.WilsonThermometerWeakJointMoments
end
