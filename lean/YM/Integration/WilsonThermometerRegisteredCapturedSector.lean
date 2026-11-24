/- All original fields and every tested scalar amplitude use the same paid marks. -/
import YM.Integration.WilsonThermometerRegisteredCapturedReading

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedSector
open RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene Finset
open Push Push.AbsoluteSums Push.Local Paths Comparison.RG02.Cumulants
open WilsonThermometerRegisteredCapturedRoster WilsonThermometerRegisteredCapturedLedger WilsonThermometerRegisteredCapturedNames
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {R:Census (Fin 3)} {α ι:Type}
variable {B:Earn.Passport n Unit} {D:Census Unit} (X:ι→Earn.Row P R G α)
variable {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
variable (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
variable (paths:Fin 3→Walk) (S:Earn.Binder B D) (t:α) (χ:R.Mode→ℂ) (A:Unit→Set ℂ)
def amplitude (x:Affinity.Wallet A):ℂ:=(x ()).val
local notation "M"=>material X ages w sold spent paths S t χ (amplitude A)

theorem original : Earn.Tableau (fun _:Unit=>(⊥:Submodule ℝ ℂ)) A M:=by
  constructor
  intro u
  have home:(S.mode.val:Finset Unit)=univ:=by
    apply eq_univ_of_forall
    intro v
    exact (Subsingleton.elim v S.front) ▸ S.east
  have singleton:Affinity.Attn (fun _:Unit=>(⊥:Submodule ℝ ℂ)) A S.mode.val (amplitude A):=by
    refine ⟨fun x y eq=>congrArg Subtype.val (eq () ?_),?_,?_⟩
    · simp [home]
    · intro v _ x a b z k l hz
      cases v
      simpa [amplitude] using hz
    · intro v _ x zero
      cases v
      exact (Submodule.mem_bot ℝ).mp zero
  let a:=roster X u.2.1.val u.2.2
  let c:ℂ:=(factor paths a σ:ℂ)*χ u.1*weights a t
  let F:ℂ→ₗ[ℝ]ℂ:=
    {toFun:=fun z=>c*z, map_add':=fun z y=>mul_add c z y,
     map_smul':=fun k z=>by simp only [Complex.real_smul,RingHom.id_apply];ring}
  exact singleton.linear F
end YM.Integration.WilsonThermometerRegisteredCapturedSector
