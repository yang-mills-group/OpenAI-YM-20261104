import YM.Integration.WilsonOriginalCompanionClearRange
import YM.Integration.WilsonOriginalCompanionLinearFiling

/-! Restore the complete constant part of the authentic gallery after the original transport. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionClearReturn
open Function Finset MeasureTheory Lattice Wilson RG Source QuadraticLocal QuadraticLocal.Earn Ac Marker Multi Push GridApprox.Nil
open MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Lodestar WilsonOriginalGalleryTwins
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalCompanionLinearFiling WilsonOriginalCompanionClearRange
open scoped Classical BigOperators
local notation "J₀" => Marks (Fin 3)
local notation "J₁" => Marks (Fin 3×Bool)
def premium:ℝ:=(Fintype.card (J₁).Mode:ℝ)^2*ceiling
variable {G:Gauge}(R:Run G){N p f u:ℕ}{T I:Type}[Countable I]{o:Fin 3→Site (R.family.side f p)}
variable (D:Gallery T I o (R.family.path.rep N p f) (J₀))(x:T)(w:Fin 3→ℝ)(hp:∀i,0<w i){a:ℝ}(expo:0≤a)
    (regular:D.E.Paid (fun i=>w i^2) (R.family.path.rep N p f).p.B a 1)(forced:D.K.Paid (fun i=>w i^2) (R.family.path.rep N p f).p.B a 1)
    (source:Integrable (D.density x) (prior G _))(uf:u≤f)

include hp expo regular forced source in
theorem original {fee:ℝ}(nn:0≤fee)
    (charged:∀s:(J₁).Mode,Poly.toll (w ∘ Prod.fst) s*
      ‖(amount R (N:=N) (p:=p) (u:=u) (f:=f) (entered D x) uf).part s‖≤fee):
    ∀s:(J₀).Mode,Poly.toll (fun i=>w i^2) s*‖(amount R (N:=N) (p:=p) (u:=u) (f:=f) (D.density x) uf).part s‖≤premium*fee:=by
  have wp(i):0<w i^2:=pow_pos (hp i) _
  let copyMap:Poly (J₀)→L[ℂ]Poly (J₁):=(duplicate (Fin 3)).toLinearMap.toContinuousLinearMap
  let c:=duplicate (Fin 3) (Poly.pass (clear D x))
  let multiple:Poly (J₁)→ₗ[ℂ] Poly (J₁):=
    { toFun:=fun z=>c*z
      map_add':=fun _ _=>mul_add ..
      map_smul':=by intros; rw [mul_smul_comm];rfl }
  let lower:=amount R (N:=N) (p:=p) (u:=u) (f:=f) (entered D x) uf
  have exactField (U:Config G (R.family.side f p)):copyMap (D.density x U)=multiple (entered D x U):=by
    change duplicate (Fin 3) (D.density x U)=c*entered D x U
    exact WilsonOriginalGalleryTwinsField.original D x (fun i=>w i^2) wp expo regular forced U
  have received:=WilsonOriginalGalleryTwinBoard.original D x w hp expo regular forced source
  have same:duplicate (Fin 3) (amount R (N:=N) (p:=p) (u:=u) (f:=f) (D.density x) uf)=c*lower:=by
    calc copyMap (amount R (N:=N) (p:=p) (u:=u) (f:=f) (D.density x) uf)=amount R (N:=N) (p:=p) (u:=u) (f:=f) (fun U=>copyMap (D.density x U)) uf:=
            transformed R copyMap _ source uf
         _=amount R (N:=N) (p:=p) (u:=u) (f:=f) (fun U=>multiple (entered D x U)) uf:=by
             exact congrArg (fun (F:Config G (R.family.side f p)→Poly (J₁))=>
               amount R (N:=N) (p:=p) F uf) (funext exactField)
         _=multiple lower:=(transformed R multiple.toContinuousLinearMap _ received.1 uf).symm
  intro s
  have bill:=WilsonOriginalCompanionClearRange.product (J':=(J₁)) (w ∘ Prod.fst) (fun i=>hp i.1) c lower (C:=ceiling) (D:=fee)
    (by unfold ceiling; positivity) nn (WilsonOriginalCompanionClearRange.upper D x w hp expo regular) charged (two s)
  rw [←same,two_toll,seal_part] at bill
  exact bill

end YM.Integration.WilsonOriginalCompanionClearReturn
end
