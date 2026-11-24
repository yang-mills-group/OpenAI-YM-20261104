import YM.Integration.WilsonOlderFreshSoftSocketCohortCash
import YM.Integration.WilsonOriginalPublicTrialFigure

/-! Issue the true inverse thermal power of each physically filed K-basis coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalDeployedVote
open Function Finset Lattice RG Wilson Source Labels WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonIndependentMatchedFiledIncome (charge allot)
open PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}(F:Labels.Frame G d)

def vector (g:ℝ)(v:F.Coeff):F.Coeff:=fun j=>v j * (((g^(F.grades j).2)⁻¹:ℝ):ℂ)

def tariff (H:ℝ):ℝ:=(1+Real.sqrt (2*H))^(Finset.univ.sup fun j:F.Index=>(F.grades j).2)

def deployed (R:Run G)(d K:ℕ)(np:ℕ×ℕ)(v:R.family.label d):(R.family.labels.level d).Coeff:=
  vector (R.family.labels.level d) (regulatorRun R.family np.1 np.2 K)
    (WilsonPositionProgramReportedField.entire R d K np v)

def wage (R:Run G)(d e:ℕ)(A:Alma (R.family.labels.level d)→ℝ)(p:ℂ→L[ℝ]ℝ)
    (M:ℝ)(E j K:ℕ):ℝ:=
  tariff (R.family.labels.level d) (R.family.path.levels.clock.hatBeta K)*
    WilsonOlderFreshSoftSocketCohortCash.wage R d e A p M E j K

theorem positive (H:ℝ):0≤tariff F H:=
  pow_nonneg (by linarith only [Real.sqrt_nonneg (2*H)]) _

private theorem real_leg (p:ℂ→L[ℝ]ℝ)(x:ℂ)(c:ℝ):p (x*(c:ℂ))=c*p x:=by
  simpa only [Complex.real_smul,smul_eq_mul,mul_comm] using p.map_smul c x

theorem coefficient (g:ℝ)(v:F.Coeff)(p:ℂ→L[ℝ]ℝ)(i:Alma F)(j:ℕ):
    coeff j (written F (vector F g v) p i)=
      ((g^(valence F i))⁻¹)*coeff j (written F v p i):=by
  by_cases live:rankS i.val.2=0
  · simp only [written,live,if_true,coeff_monomial]
    split
    · exact real_leg p _ _
    · simp
  · simp [written,live]

theorem original (R:Run G)(N per K:ℕ)(live:K≤N)(e:ℕ)(v:F.Coeff)(p:ℂ→L[ℝ]ℝ)
    (A:Alma F→ℝ)(nn:∀i,0≤A i):
    let g:=regulatorRun R.family N per K
    charge e (written F (vector F g v) p) A≤
      tariff F (R.family.path.levels.clock.hatBeta K)*charge e (written F v p) A:=by
  intro g
  let H:=R.family.path.levels.clock.hatBeta K
  have gpos:0<g:=ActualRunKernelPackets.regulator_pos R N per K live
  have band: R.family.path.β N per K ≤2*H:=(R.makes.wilson.represents N per K live).band.2
  have root:g⁻¹≤1+Real.sqrt (2*H):=by
    change ((Real.sqrt (R.family.path.β N per K))⁻¹)⁻¹≤_
    rw [inv_inv]
    exact (Real.sqrt_le_sqrt band).trans (le_add_of_nonneg_left zero_le_one)
  have one:1≤1+Real.sqrt (2*H):=le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have bound (i:Alma F):|(g^(valence F i))⁻¹|≤tariff F H:=by
    rw [abs_of_pos (inv_pos.mpr (pow_pos gpos _)),←inv_pow]
    exact (pow_le_pow_left₀ (inv_pos.mpr gpos).le root _).trans
      (pow_le_pow_right₀ one (Finset.le_sup (s:=univ) (f:=fun j:F.Index=>(F.grades j).2) (mem_univ (sheet F i))))
  unfold charge allot
  simp only [mul_sum]
  refine sum_le_sum fun i _=>sum_le_sum fun j _=>sum_le_sum fun t _=>?_
  rw [coefficient,abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_right (bound i) (mul_nonneg (abs_nonneg _) (nn i))

theorem filed (R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)(b:∀i,(R.family.labels.level (d i)).Index)
    (v:∀i,(R.family.labels.level (d i)).Coeff)(g:ℝ):
    (∏i,vector (R.family.labels.level (d i)) g (v i) (b i))=WilsonOriginalPublicTrialFigure.weight R d g v b:=rfl

end YM.Integration.WilsonOriginalPublicNodalDeployedVote
end
