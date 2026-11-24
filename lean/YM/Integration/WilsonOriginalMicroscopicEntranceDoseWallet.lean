import YM.Integration.WilsonOriginalMicroscopicEntranceBirthCapital
import YM.Integration.WilsonOriginalMicroscopicEntranceDoseGrid

/-! Pay a bounded common test amplitude before either regulator and restore the Haar-integrable reached word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDoseWallet
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker PhysicalNext PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

theorem original {G:Gauge}(R:Run G){d:Fin 3→ℕ}
    (fitted:∀j,R.family.label (d j))(factor dose:Fin 3→ℂ)
    {B S:ℝ}(cap:∀j,‖dose j‖≤S)
    (paid:∀j,(R.family.labels.level (d j)).coeffSize (factor j • fitted j)≤B)(j:Fin 3):
    (R.family.labels.level (d j)).coeffSize ((dose j*factor j) • fitted j)≤S*B:=by
  rw [mul_smul]
  have same:(R.family.labels.level (d j)).coeffSize (dose j • (factor j • fitted j))=
      ‖dose j‖*(R.family.labels.level (d j)).coeffSize (factor j • fitted j):=by
    simp only [Labels.Frame.coeffSize,Pi.smul_apply,norm_smul,Finset.mul_sum]
  rw [same]
  exact mul_le_mul (cap j) (paid j) (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) ((norm_nonneg _).trans (cap j))

theorem integrable {X:Type*}[MeasurableSpace X]{μ:Measure X}(D:X→ℝ)(b:X→ℂ)(a:ℂ)
    (h:Integrable (fun U=>D U • b U) μ):Integrable (fun U=>D U • (a*b U)) μ:=by
  convert h.const_mul a using 1
  ext U
  simp only [Complex.real_smul]
  ring

end YM.Integration.WilsonOriginalMicroscopicEntranceDoseWallet
end
