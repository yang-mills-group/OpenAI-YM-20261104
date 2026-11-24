import YM.Integration.FVA1Physical.Wilson.IteratedBankGate
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock
import YM.Integration.FVA1Physical.Round2.FormalFieldTruncation

/-! Pad a genuinely rendered incoming source to a larger comparison order with
zero higher coefficients. This preserves the physical reading on every field
and the first normalized Wilson coefficients, including the full denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset Matrix MvPolynomial Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Bulk MSbar.Bakery MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic
open MSbar.Rolling MSbar.Midpoint MSbar.Bakery.Film MSbar.Bakery.Portal Push.Uniform
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical
variable {G:Gauge}

theorem crop_bank_read {σ:Type} {p:ℕ} (d:ℕ) (T:PowerSeries (Pot σ)) (g:ℝ) (Z:View σ) :
    clockReading (p+d) g (cropAction p T) Z = clockReading p g T Z := by
  unfold clockReading taste
  rw [show p+d+1=p+1+d by omega,Finset.sum_range_add]
  simp only [picture,PowerSeries.coeff_map,cropAction,PowerSeries.coeff_mk]
  have tail: (∑ j∈range d,g^(p+1+j)*eval Z (if p+1+j ≤ p then PowerSeries.coeff (p+1+j) T else 0))=0 := by
    apply sum_eq_zero
    intro j _
    simp only [if_neg (show ¬ p+1+j≤p by omega),map_zero,mul_zero]
  rw [tail,add_zero]
  apply sum_congr rfl;intro i hi
  rw [if_pos (Nat.le_of_lt_succ (mem_range.mp hi))]

theorem BankPaid.pad {c:Side} {b:Site c} {y δ:ℝ} (hy:0 ≤ y) {p s m:ℕ} {T:Nesting G c}
    (paid:BankPaid b y s p m δ T) (n:ℕ) :
    BankPaid b y s n m δ (cropAction p T) := by
  intro i _
  by_cases hi:i≤p
  · simpa only [cropAction,PowerSeries.coeff_mk,if_pos hi] using paid i hi
  simp only [cropAction,PowerSeries.coeff_mk,if_neg hi,totalDegree_zero,Nat.zero_le,true_and]
  exact Quote.nill (Real.rpow_nonneg hy _)

theorem BankPaid.enlarge_degree {c:Side} {b:Site c} {y δ:ℝ} {p s m m':ℕ} {T:Nesting G c}
    (paid:BankPaid b y s p m δ T) (hm:m ≤ m') : BankPaid b y s p m' δ T :=
  fun i hi=>⟨(paid i hi).1.trans hm,paid.through m' hi⟩

theorem crop_emission_prefix (A:Issue G) (χ:ChartRatio G) (T:Nesting G A.f)
    (kind:Kind A.T) (pd:(mold A.pre A.F A.v).PosDef) (p d:ℕ) :
    Lap p (emittedRows A χ (enterRows A (cropAction p T)) (p+d)) (emittedRows A χ (enterRows A T) p) := by
  have ok:=well A.F A.v χ A.T kind
  have same:Lap p (normalizedRows A χ (enterRows A (cropAction p T)) (p+d))
      (normalizedRows A χ (enterRows A T) p) := by
    apply grow_prefix (straight A.F G) pd.inv ok ok (fun _ _=>rfl) _ (by omega) (Nat.lt_succ_self p)
    intro i hi
    simp only [enterRows,PowerSeries.coeff_map,cropAction,PowerSeries.coeff_mk,if_pos hi]
  intro i hi
  simp only [emittedRows,PowerSeries.coeff_map,same i hi]

end YM.Integration.FVA1Physical.Wilson
