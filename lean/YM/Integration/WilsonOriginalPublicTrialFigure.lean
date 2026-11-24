import YM.Integration.WilsonOriginalPublicTrialInput
import YM.Integration.WilsonPositionProgramCopyTop

/-! The finite measured input at the fixed trial station on every auxiliary period. -/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

namespace YM.Integration.WilsonOriginalPublicTrialFigure
open Finset Lattice Wilson RG Source Labels RegulatorIR.FVAAlt2
open Pert.Asymptotics Extra.Histories PhysicalNext PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalMicroscopicGuardedTrial
open WilsonOriginalPublicTrialInput
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
local notation "F" j:max => R.family.labels.level (d j)

def amount (g:ℝ)(v:∀j,(F j).Coeff)(i:I)(a:(F i).Index):ℂ:=
  v i a * ((g^((F i).grades a).2:ℝ)⁻¹:ℝ)

def weight (g:ℝ)(v:∀j,(F j).Coeff)(a:∀i,(F i).Index):ℂ:=
  ∏ i,amount R d g v i (a i)

def measured (g:ℝ)(v:∀j,(F j).Coeff)(z:I→ Cover){n:Side}(U:Config G n):ℂ:=
  ∏i,∑a,amount R d g v i a*(R.family.localSection (d i)).places (Pi.single a 1) (wrap n (z i)) U

/-- The same numerical coefficients multiply the same registered group functions
on each auxiliary side. This includes empty products and constant basis vectors. -/
theorem opened (g:ℝ)(v:∀j,(F j).Coeff)(z:I→ Cover)(n:Side)(U:Config G n):
    measured R d g v z U=∑a,weight R d g v a*
      ((Sound.Figure.prop R (fun _:Unit=>z) d a ()).Vt n U:ℝ):=by
  unfold measured
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  rw [prod_mul_distrib]
  congr 1
  have h:=congrFun (Boot.combined R univ d a z n) U
  simpa only [Finset.prod_apply,Function.comp_apply,Sound.Figure.prop,Boot.scout] using h.symm

variable (grades j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (grades a))
    (before:∀a,j a≤K)(registered:Indexed R grades j target η M Y)
    (N per:ℕ)(live:K<N)(child:I→Fin 3)
local notation "v" => fitted R grades j K target η M Y before registered N per
local notation "v₀" => vector R grades j K target η M Y before registered N per
local notation "g" => regulatorRun R.family N per K

include live in
/-- At the original period this declared source is the fitted unguarded physical
trial itself. Each actual position may have an independently chosen cover lift. -/
theorem original (o:Fin 3→Site (R.family.side K per))(z:I→ Cover)
    (lift:∀i,wrap (R.family.side K per) (z i)=o (child i))(U:Config G (R.family.side K per)):
    (∏i,raw R grades N per K o v (child i) U)=
      ∑a,weight R (grades ∘ child) g (fun i=>v₀ (child i)) a*
        ((Sound.Figure.prop R (fun _:Unit=>z) (grades ∘ child) a ()).Vt _ U:ℝ):=by
  rw [←opened]
  apply prod_congr rfl
  intro i _
  rw [(WilsonOriginalPublicTrialInput.original R grades j K target η M Y before registered N per live).2.1 o (child i) U]
  apply sum_congr rfl
  intro a _
  rw [lift i]
  simp only [Function.comp_apply,amount,WilsonPositionProgramBlockedTrialFiling.atomAt,
    Complex.real_smul,Complex.ofReal_inv,mul_assoc]
  rfl

end YM.Integration.WilsonOriginalPublicTrialFigure
end
