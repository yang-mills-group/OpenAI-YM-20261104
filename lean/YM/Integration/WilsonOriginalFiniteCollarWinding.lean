import YM.Integration.WilsonMarkedIndependentMixedOrderedWinding

/-! At a fixed physical report every marked date, source and downstream observer
in this collar is fixed before the upper cutoff. The larger auxiliary torus may
depend on all of them. No convergence of that auxiliary finite-cutoff sequence
at a fixed physical period is needed to remove its signed error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiniteCollarWinding
open Filter Finset Lattice Wilson RG WilsonCoeffUV.Winding
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G){I:Type*}
def bound (j per:ℕ)(A B σ τ D:ℝ):ℝ:=
  A*Real.exp (σ/8*D)*catchW (σ/8) (R.family.side j per).val+
  B*catchW τ (R.family.side j per).val

theorem single (j per:ℕ)(big:Side)(divides:(R.family.side j per).val∣big.val)
    {A B σ τ D:ℝ}(bp:0≤B)(tp:0<τ):
    A*Real.exp (-(((σ/2)/2)*(((R.family.side j per).val:ℝ)-D))/2)+
      B*catchW τ big.val ≤ bound R j per A B σ τ D:=by
  have size:(R.family.side j per).val≤big.val:=Nat.le_of_dvd big.pos divides
  have smaller:catchW τ big.val ≤ catchW τ (R.family.side j per).val:=by
    unfold catchW
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left (by exact_mod_cast size) (neg_nonpos.mpr tp.le)
  unfold bound
  have affine:-(((σ/2)/2)*(((R.family.side j per).val:ℝ)-D))/2 =
      σ/8*D+(-(σ/8))*((R.family.side j per).val:ℝ):=by ring
  rw [affine,Real.exp_add]
  unfold catchW at smaller ⊢
  rw [←mul_assoc]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left smaller bp)

theorem disappears (j:ℕ){A B σ τ D:ℝ}(sp:0<σ)(tp:0<τ):
    Tendsto (fun per=>bound R j per A B σ τ D) atTop (𝓝 0):=by
  have a:= (WilsonMarkedIndependentMixedOrderedWinding.disappears (b:=j) R (σ/8) (by positivity)).const_mul (A*Real.exp (σ/8*D))
  have b:= (WilsonMarkedIndependentMixedOrderedWinding.disappears (b:=j) R τ tp).const_mul B
  simpa only [bound,mul_zero,add_zero] using a.add b

theorem schedule (dates:Finset I)(j:I→ℕ)(A B σ τ D:I→ℝ)
    (sp:∀i∈dates,0<σ i)(tp:∀i∈dates,0<τ i):
    Tendsto (fun per:ℕ=>∑i∈dates,bound R (j i) per (A i) (B i) (σ i) (τ i) (D i)) atTop (𝓝 0):=by
  simpa only [sum_const_zero] using
    tendsto_finsetSum dates (fun i hi=>disappears (A:=A i) (B:=B i) (D:=D i) R (j i) (sp i hi) (tp i hi))

theorem ultraviolet {X:Type*}[NormedAddCommGroup X](dates:Finset I)(j:I→ℕ)(K:ℕ)
    (A B σ τ D:I→ℝ)(sp:∀i∈dates,0<σ i)(tp:∀i∈dates,0<τ i)(bp:∀i∈dates,0≤B i)
    (board:ℕ→ℕ→I→Side)(error:ℕ→ℕ→I→X)
    (paid:∀ᶠ per:ℕ in atTop,∀N, K ≤ N → ∀i∈dates,
      (R.family.side (j i) per).val ∣ (board N per i).val ∧
      ‖error N per i‖ ≤ A i*Real.exp (-(((σ i/2)/2)*(((R.family.side (j i) per).val:ℝ)-D i))/2)+
        B i*catchW (τ i) (board N per i).val):
    ∀ε:ℝ,0 < ε → ∀ᶠ per:ℕ in atTop,∀N,K ≤ N → (∑i∈dates,‖error N per i‖) < ε:=by
  intro ε ep
  filter_upwards [paid,(schedule R dates j A B σ τ D sp tp).eventually_lt_const ep] with per fees small
  intro N top
  refine lt_of_le_of_lt (sum_le_sum ?_) small
  intro i hi
  have h:=fees N top i hi
  exact h.2.trans (single R (j i) per _ h.1 (bp i hi) (tp i hi))

end YM.Integration.WilsonOriginalFiniteCollarWinding
end
