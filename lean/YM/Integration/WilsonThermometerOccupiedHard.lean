import YM.Integration.WilsonThermometerMixedAmplitude
import YM.Integration.WilsonOriginalFiledHardRebill
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedHard
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached RG3.Letters MeasureTheory Comparison.RG02.Order
open WilsonThermometerMixedAmplitude
open scoped Classical BigOperators
variable {R:Marker.Census (Fin 3)} {G:Gauge} {n:Side} {P:Rep G n} {o:Fin 3→Site n}
  {X ι:Type*} {p:BudgetPoint} {F:ℕ→ForcedAddress G n} {K:Code G n} {q T:ℂ}

/-- Keep the quiet value at every original address and scale each nonempty coefficient. -/
def amount (c:ℂ)(s:R.Mode):ℂ:=if s=R.quiet then 1 else c
def paint (c:ℂ)(p:Poly R):Poly R:=Poly.inject fun s=>amount c s*p.part s

def hard (c:ℂ)(A:Hard X p F K o R):Hard X p F K o R where
  hard x i U:=paint c (A.hard x i U)
  locality x i:=by
    refine ⟨fun t U=>congrArg (paint c) ((A.locality x i).gauge t U),?_,
      fun U V h e=>congrArg (paint c) ((A.locality x i).reads U V h e),?_⟩
    · have cont:Continuous (paint (R:=R) c):=continuous_pi (fun s=>continuous_const.mul (Poly.get s).continuous)
      exact cont.measurable.comp (A.locality x i).borel
    · intro U s live
      apply (A.locality x i).carry U s
      intro hg
      exact live (by change amount c s*(A.hard x i U).part s=0;rw [hg,mul_zero])
  charged x i U live:=by
    apply A.charged x i U
    intro hg
    apply live
    ext1 s
    change amount c s*(A.hard x i U).part s=0
    rw [hg,Poly.part_nil,mul_zero]
  quiet x i U:=by
    change amount c R.quiet*(A.hard x i U).part R.quiet=_
    rw [show amount c R.quiet=1 by simp [amount],one_mul,A.quiet]

theorem origin (A:Hard X p F K o R) (x:X) (i:ℕ) (U:Config G n) (s:R.Mode):
    ((hard 0 A).hard x i U).part s = if s=R.quiet then (K i U:ℂ) else 0 := by
  change amount 0 s * (A.hard x i U).part s = _
  by_cases h:s=R.quiet
  · simp [amount,h,A.quiet]
  · simp [amount,h]

theorem identity (A:Hard X p F K o R) (x:X) (i:ℕ) (U:Config G n):
    (hard 1 A).hard x i U = A.hard x i U :=by
  ext1 s
  change amount 1 s * _ = _
  simp [amount]

theorem paid (A:Hard X p F K o R) {w:Fin 3→ℝ} {B:ℕ} {a r m:ℝ}
    (z:ℂ) (large:1 ≤ m) (within:‖z‖ ≤ m) (pos:∀v,0<w v)
    (old:A.Paid w B a r):(hard z A).Paid w B a (m*r):=by
  have funded:0 ≤ m:=zero_le_one.trans large
  have cap (s:R.Mode):‖amount z s‖ ≤ m:=by
    by_cases h:s=R.quiet
    · simpa [amount,h] using large
    · simpa [amount,h] using within
  obtain ⟨f,covers,bill⟩:=old.wages
  refine ⟨fun i=>(m:ℂ) • f i,?_,?_⟩
  · intro i x U s
    obtain ⟨un,real⟩:=covers i x U s
    change ‖amount z s*(A.hard x i U).part s‖ ≤ ((m:ℂ)*(f i).part s).re ∧
      ((m:ℂ)*(f i).part s).im=0
    simp only [norm_mul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,real,mul_zero,zero_mul,add_zero,sub_zero]
    exact ⟨mul_le_mul (cap s) un (norm_nonneg _) funded,trivial⟩
  intro root
  apply budget_mono (budget_scale funded (bill root))
  · intro i
    split
    · exact mul_nonneg (Poly.nonnegative pos _) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    by_cases keep : root∈(F i).support
    · simp only [if_pos keep]
      have rate:Poly.price w ((m:ℂ) • f i)=m*Poly.price w (f i):=by
        unfold Poly.price
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Poly.part_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg funded]
        ring
      rw [rate,mul_assoc]
    · simp [keep]

end YM.Integration.WilsonThermometerOccupiedHard
