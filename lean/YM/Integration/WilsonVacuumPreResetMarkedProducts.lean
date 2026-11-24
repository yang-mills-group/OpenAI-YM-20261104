import YM.Integration.WilsonVacuumPreResetMarkedTensorSlope

/-! Finite sup-norm estimates for the actual marked tensor products in
the ordinary cofactor and the normalized connected logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedProducts
open Function Finset WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open scoped Classical BigOperators
variable {ι U:Type} [DecidableEq ι] {D:ι→ℕ} {J I:Finset ι}

def Bounded {V:Type} [NormedAddCommGroup V](e r:ℕ)(F:Pal V U)(M:ℝ):Prop:=
  ∀i≤e,∀s≤r,∀x,‖F i s x‖≤M

def tariff(e r:ℕ):ℝ:=(e+1:ℕ)*(r+1:ℕ)

theorem sum {α V:Type} [NormedAddCommGroup V] (s:Finset α)(F:α→V)(M:ℝ)
    (paid:∀a∈s,‖F a‖≤M):‖∑a∈s,F a‖≤(s.card:ℝ)*M:=by
  apply (norm_sum_le ..).trans
  exact (Finset.sum_le_sum paid).trans_eq (by simp)

private theorem averaged {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
    {r:ℕ}(F:Ten V U r)(B:ℝ)(paid:∀x,‖F x‖≤B)(x:Fin r→U):‖swirl F x‖≤B:=by
  let n:ℝ:=Fintype.card (Equiv.Perm (Fin r))
  have pos:0<n:=by dsimp [n];exact_mod_cast Fintype.card_pos
  simp only [swirl,Pi.smul_apply,Finset.sum_apply,norm_smul]
  change ‖n⁻¹‖*‖∑ q:Equiv.Perm (Fin r),F (x ∘ q)‖≤B
  rw [Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr pos).le]
  apply (mul_le_mul_of_nonneg_left (sum (univ:Finset (Equiv.Perm (Fin r))) (fun q=>F (x ∘ q)) B (fun q _=>paid (x ∘ q))) (inv_pos.mpr pos).le).trans
  simp only [Finset.card_univ,←mul_assoc]
  change n⁻¹*n*B≤B
  rw [inv_mul_cancel₀ pos.ne',one_mul]

theorem foam_bound (j:J⊆I)(P:Pal (Pen D J) U)(Q:Pal (Pen D (I\J)) U)
    (e r:ℕ)(A B:ℝ)(apos:0≤A)(bpos:0≤B)(left:Bounded e r P A)(right:Bounded e r Q B):
    Bounded e r (foam j P Q) (tariff e r*(A*B)):=by
  intro i hi l hl x
  simp only [foam,Finset.sum_apply]
  have pair(u:ℕ×ℕ)(hu:u∈HasAntidiagonal.antidiagonal i):
      ‖cob j (P u.1) (Q u.2) l x‖≤(l+1:ℕ)*(A*B):=by
    have cou:u.1+u.2=i:=by simpa using hu
    apply averaged
    intro y
    simp only [Finset.sum_apply]
    apply (sum _ _ (A*B) _).trans_eq
    · simp
    · intro z hz
      have slots:z.1+z.2=l:=by simpa using hz
      simp only [cobT,dif_pos slots,waveJoy]
      exact (joy_norm ..).trans (mul_le_mul (left _ (by omega) _ (by omega) _)
        (right _ (by omega) _ (by omega) _) (norm_nonneg _) apos)
  apply (sum _ _ _ pair).trans
  simp only [Nat.card_antidiagonal]
  dsimp only [tariff]
  push_cast at *
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (by exact_mod_cast (show i+1≤e+1 by omega)) (by exact_mod_cast (show l+1≤r+1 by omega)) (by positivity) (by positivity))
    (mul_nonneg apos bpos)

theorem time_bound (j:J⊆I)(P:Layers (Pen D J) U)(Q:Layers (Pen D (I\J)) U)
    (e r h:ℕ)(A B:ℝ)(apos:0≤A)(bpos:0≤B)
    (left:∀u≤h,Bounded e r (P u) A)(right:∀u≤h,Bounded e r (Q u) B):
    ∀v≤h,Bounded e r (foamT j P Q v) ((h+1:ℕ)*(tariff e r*(A*B))):=by
  intro v hv i hi l hl x
  simp only [foamT,Finset.sum_apply]
  apply (sum _ _ _ (fun uv huv=>?_)).trans
  · simp only [Nat.card_antidiagonal]
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hv)
    dsimp only [tariff];positivity
  · have stage:uv.1+uv.2=v:=by simpa using huv
    exact foam_bound j _ _ e r A B apos bpos (left uv.1 (by omega)) (right uv.2 (by omega)) i hi l hl x

end YM.Integration.WilsonVacuumPreResetMarkedProducts
end
