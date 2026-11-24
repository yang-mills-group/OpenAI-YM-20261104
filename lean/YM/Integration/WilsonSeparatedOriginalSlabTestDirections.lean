import YM.Integration.WilsonSeparatedOriginalSlabTestNorm

/-! Every original mixed physical read factors continuously through just its declared derivative of the shared external test. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabTestDirections
open Function Finset Lattice RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Pulse
open scoped Classical BigOperators ContDiff
variable {V:Type}[Fintype V][DecidableEq V]

private theorem bounded {X Y:Type*}[AddCommGroup X][Module ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
    (j:X →ₗ[ℝ] Y)(l:X →ₗ[ℝ] ℂ)(same:∀f g:X,j f=j g → l f=l g):
    ∃C:ℝ,0≤C ∧ ∀f,‖l f‖ ≤ C*‖j f‖:=by
  obtain ⟨u,hu⟩:=j.rangeRestrict.exists_rightInverse_of_surjective j.range_rangeRestrict
  let L:LinearMap.range j →L[ℝ] ℂ:=(l.comp u).toContinuousLinearMap
  refine ⟨‖L‖,L.opNorm_nonneg,?_⟩
  intro f
  have hx:j (u (j.rangeRestrict f))=j f:=congrArg Subtype.val (LinearMap.congr_fun hu (j.rangeRestrict f))
  rw [←same _ _ hx]
  exact L.le_opNorm _

private instance finite (n:ℕ):FiniteDimensional ℝ (Cloud V [×n]→L[ℝ] ℂ):=by
  induction n with
  | zero=>exact FiniteDimensional.of_injective ((continuousMultilinearCurryFin0 ℝ (Cloud V) ℂ).toLinearIsometry.toLinearMap) (continuousMultilinearCurryFin0 ℝ (Cloud V) ℂ).injective
  | succ n ih=>
    letI:=ih
    exact FiniteDimensional.of_injective ((continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (n+1)=>Cloud V) ℂ).toLinearIsometry.toLinearMap) (continuousMultilinearCurryLeftEquiv ℝ _ _).injective

private def jet (q:ℕ):Wave V →ₗ[ℝ] (Cloud V [×q]→L[ℝ] ℂ) where
  toFun f:=iteratedFDeriv ℝ q f.val 0
  map_add' f g:=iteratedFDeriv_add_apply (lit f q).contDiffAt (lit g q).contDiffAt
  map_smul' c f:=iteratedFDeriv_const_smul_apply (a:=c) (lit f q).contDiffAt

def order (s:V→ℕ)(a:(i:V)→Letter (s i)):ℕ:=pegs s a (Finset.univ.toList)

theorem original (s:V→ℕ)(a:(i:V)→Letter (s i)):
    ∃C:ℝ,0≤C ∧ ∀(f:Wave V)(x:Cloud V),
      ‖(perform s a f).val x‖ ≤ C*‖iteratedFDeriv ℝ (order s a) f.val x‖:=by
  let op:Wave V →ₗ[ℝ] Wave V:=(perform s a).restrictScalars ℝ
  let l:Wave V →ₗ[ℝ] ℂ:=
    { toFun:=fun f=>(op f).val 0
      map_add':=fun f g=>by rw [map_add];rfl
      map_smul':=fun c f=>by rw [map_smul];rfl }
  obtain ⟨C,c,price⟩:=bounded (jet (V:=V) (order s a)) l (fun f g eq=>performance s a eq)
  refine ⟨C,c,?_⟩
  intro f x
  have shifted:l (fork 1 x f)=(perform s a f).val x:=by
    change (machine s a (Finset.univ.toList) (fork 1 x f)).val 0=_
    rw [machine_roll]
    simp only [Complex.ofReal_one,one_pow,one_smul]
    change (perform s a f).val (x+(1:ℝ) • 0)=_
    simp
  have translated:jet (order s a) (fork 1 x f)=iteratedFDeriv ℝ (order s a) f.val x:=by
    change iteratedFDeriv ℝ _ (fun z=>f.val (x+(1:ℝ) • z)) 0=_
    simp only [one_smul]
    rw [iteratedFDeriv_comp_add_left,add_zero]
  simpa only [shifted,translated] using price (fork 1 x f)

theorem grades (s:V→ℕ)(a:(i:V)→Letter (s i)):order s a ≤ ∑i:V,s i:=pegs_cost s a

end YM.Integration.WilsonSeparatedOriginalSlabTestDirections
