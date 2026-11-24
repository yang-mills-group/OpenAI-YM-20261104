import YM.Integration.WilsonOriginalPublicFigureProjected
import YM.Integration.WilsonPositionProgramTrialSurvey

/-! Invert the measured finite survey's own Wick subtraction before mapping
the filed numerical label into the on-shell position space. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 480000
namespace YM.Integration.WilsonOriginalPublicFigureWick
open Function Finset Lattice Wilson RG Labels PhysicalNext.Repeat.Legato PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicFigureProjected (change)
open WilsonMaxwellThermometerPositionCurrency (received physicalWord)
open WilsonThermometerPositionTunedSlope (Columns paid price)
open WilsonThermometerPositionTunedCorrection (surveyed residual)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical BigOperators
variable {G:Gauge}{h n:ℕ}(W:Initialize G)(F:Labels.Frame G h)

def unwick:F.Coeff→ₗ[ℂ]Label G h:=(W.surveys h).insertW 1 ∘ₗ F.coords.symm.toLinearMap
def project:F.Coeff→ₗ[ℂ]Sec G h:=(observable G h).rangeRestrict ∘ₗ unwick W F
def remainder:F.Coeff→ₗ[ℂ]Label G h:=unwick W F-On.sectionMap h ∘ₗ project W F

theorem invisible (v:F.Coeff):observable G h (remainder W F v)=0:=by
  rw [remainder,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,On.recovers]
  exact sub_self _

theorem entered (P:Period)(T:P.Tree)(o:P.Sites)(v:F.Coeff):
    Bare.raw T (W.surveys h) o (F.coords.symm v).val=
      Bare.column T (W.surveys h) o (unwick W F v):=by
  rw [Bare.column_formula,unwick,LinearMap.comp_apply]
  rw [(W.surveys h).wick_recovers]
  rfl

def superior (X:Sample n)(o:X.F.Sites)(v:F.Coeff):Bare.Series (W.tree X.F.p) G:=
  ∑k:Fin (h+1),(
    Bare.column (W.tree X.F.p) (W.surveys h) o
      (On.sectionMap h (en (Nat.le_of_lt_succ k.isLt) (part h k.val (project W F v))))-
    On.stencil W.hol (W.surveys k.val) X.F.p (W.tree X.F.p) o (part h k.val (project W F v)))

theorem split (X:Sample n)(o:X.F.Sites)(v:F.Coeff):
    Bare.raw (W.tree X.F.p) (W.surveys h) o (F.coords.symm v).val=
      physicalWord W X 1 (project W F v) o + superior W F X o v+
        Bare.column (W.tree X.F.p) (W.surveys h) o (remainder W F v):=by
  rw [entered,remainder,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,
    superior,Finset.sum_sub_distrib,← map_sum,←map_sum,enfits,physicalWord]
  simp only [Complex.ofReal_one,one_pow,inv_one,one_smul]
  abel

theorem engineering (X:Sample n)(a:ℝ)(nonzero:a≠0)(p:Sec G h):
    received X a ((a:ℂ)^h • p)=received X 1 p:=by
  unfold received
  apply sum_congr rfl
  intro k _
  simp only [map_smul,smul_smul,Complex.ofReal_one,one_pow,div_one]
  congr 1
  exact div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr nonzero))

theorem priced_word (X:Sample n)(a:ℝ)(nonzero:a≠0)(o:X.F.Sites)(v:F.Coeff):
    Bare.raw (W.tree X.F.p) (W.surveys h) o (F.coords.symm v).val=
      regal W h X o (received X a ((a:ℂ)^h • project W F v))+
        superior W F X o v+Bare.column (W.tree X.F.p) (W.surveys h) o (remainder W F v):=by
  rw [engineering X a nonzero,WilsonMaxwellThermometerPositionCurrency.single]
  exact split W F X o v

end YM.Integration.WilsonOriginalPublicFigureWick
end
