import YM.QuadraticLocal.Fk.Capsule
import YM.Next.RANK.LineBox

/-! Coefficients of one independently deposited curved row.  The ordinary
Taylor coefficients below the prescribed rank vanish before the Laurent
shift.  The surviving coefficients are the original signed mark receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.RowCoefficients
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry
open Next PertExtension.Series Comparison.RG02
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {P : Passport n V} {Γ : Census V}

private theorem shifted (g : ℝ) (hg : 0<g) (e r p : ℕ) (he : e≤p) (f : ℕ→ℝ)
    (zero : ∀j<r,f j=0) :
    g^((e:ℤ)-r)*(∑j∈range (p-e+r+1),g^j*f j) =
      ∑u∈range (p+1),g^u*(if e≤u then f (u-e+r) else 0) := by
  have left : p-e+r+1=r+(p-e+1) := by omega
  have right : p+1=e+(p-e+1) := by omega
  conv_lhs => rw [left,sum_range_add]
  conv_rhs => rw [right,sum_range_add]
  have z1 : (∑j∈range r,g^j*f j)=0 := by
    apply sum_eq_zero; intro j hj; rw [zero j (mem_range.mp hj),mul_zero]
  have z2 : (∑j∈range e,g^j*(if e≤j then f (j-e+r) else 0))=0 := by
    apply sum_eq_zero; intro j hj; rw [if_neg (Nat.not_le_of_lt (mem_range.mp hj)),mul_zero]
  rw [z1,z2,zero_add,zero_add,mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [if_pos (by omega : e≤e+j),show e+j-e+r=r+j by omega,←mul_assoc]
  congr 1
  rw [←zpow_natCast g (r+j),←zpow_add₀ hg.ne',←zpow_natCast g (e+j)]
  congr 1
  push_cast
  ring

theorem named (T : Row P Γ G X) (A : Stationary.Link G n) {p : ℕ} (he : T.lamp.e≤p)
    (g : ℝ) (hg : 0<g) :
    g^T.lamp.lag * (∑j∈range (p-T.lamp.e+T.lamp.r+1),
      g^j*PertExtension.Series.Radial.jet (Helmet.frame T.atom T.center) j A) =
        ∑e∈range (p+1),g^e*T.markReceipt e A := by
  apply shifted g hg T.lamp.e T.lamp.r p he
  intro j hj
  unfold PertExtension.Series.Radial.jet
  rw [(Helmet.frameGrade T.atom T.center).vanish j hj]
  simp

theorem coefficient (T : Row P Γ G X) (x : X) (j : ℕ) (A : Stationary.Link G n) :
    ((j.factorial:ℝ)⁻¹) • iteratedDeriv j
        (fun t:ℝ=>T.nominal 1 x (Stationary.input G n (t • A))) 0 =
      T.paint x * (PertExtension.Series.Radial.jet (Helmet.frame T.atom T.center) j A : ℝ) := by
  let F := Helmet.frame T.atom T.center
  let L : ℝ→L[ℝ]ℂ := T.paint x • Complex.ofRealCLM
  have smooth : ContDiffAt ℝ j F 0 := (Helmet.frameGrade T.atom T.center).smooth.of_le le_top
  have represented : (fun t:ℝ=>T.nominal 1 x (Stationary.input G n (t • A))) =
      (fun t:ℝ=>(L ∘ F) (t • A)) := by
    funext t
    simp [F,L,QuadraticLocal.Earn.Row.nominal,QuadraticLocal.Earn.Row.grain,
      Helmet.frame,Pi.smul_apply,smul_eq_mul]
  rw [represented,Next.Rank.Spindle.upon A (L ∘ F) j (L.contDiff.contDiffAt.comp 0 smooth),
    L.iteratedFDeriv_comp_left smooth (by exact_mod_cast le_refl j)]
  simp [PertExtension.Series.Radial.jet,L,F,smul_eq_mul]
  ring

end YM.Integration.WilsonPhysicalMarkedDefect.RowCoefficients
