import YM.Integration.WilsonSeparatedOriginalSlabFourierBudget
import YM.Integration.WilsonSeparatedOriginalSlabPeriodCells

/-! The signed Fourier expansion of an actual compactly supported profile on its original central cube. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabCompactFourier
open Filter Set Function Metric MeasureTheory UnitAddTorus WilsonSeparatedOriginalSlabFourierOrbit
open WilsonSeparatedOriginalSlabFourierScore WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabPeriodCells
open scoped Topology BigOperators Classical ContDiff
variable {J:Type*}[Fintype J]{a:Room J}{ρ:ℝ}{f:Room J→ℂ}

omit [Fintype J] in
private theorem opens : IsOpenQuotientMap (@wrap J):=by
  have h:∀i:J,IsOpenQuotientMap (fun x:ℝ=>(x:UnitAddCircle)):=fun _=>QuotientAddGroup.isOpenQuotientMap_mk
  exact ⟨onto,continuous_pi fun i:J=>(h i).continuous.comp (continuous_apply i),show IsOpenMap (Pi.map (fun _:J=>fun x:ℝ=>(x:UnitAddCircle))) from
    IsOpenMap.piMap (fun i=>(h i).isOpenMap) (Eventually.of_forall fun i=>(h i).surjective)⟩

def descended (a:Room J)(ρ:ℝ)(f:Room J→ℂ)(y:UnitAddTorus J):ℂ:=orbit a ρ 1 f ((onto y).choose)

theorem reads (small:ρ+ρ<1)(live:support f⊆closedBall a ρ)(x:Room J):
    descended a ρ f (wrap x)=orbit a ρ 1 f x:=
  periodic f _ _ zero_lt_one small live (loops (onto (wrap x)).choose_spec)

def profile (smooth:ContDiff ℝ ∞ f)(small:ρ+ρ<1)(live:support f⊆closedBall a ρ):C(UnitAddTorus J,ℂ) where
  toFun:=descended a ρ f
  continuous_toFun:= opens.isQuotientMap.continuous_iff.mpr (by
    rw [show descended a ρ f ∘ wrap=orbit a ρ 1 f from funext (reads small live)]
    exact (round smooth live zero_lt_one small).continuous)

theorem bill (small:ρ+ρ<1)(live:support f⊆closedBall a ρ)(n:ℕ){B:ℝ}(hB:0≤B)
    (jets:∀x,‖iteratedFDeriv ℝ n f x‖≤B)(x:Room J):‖iteratedFDeriv ℝ n (orbit a ρ 1 f) x‖≤B:=by
  rcases orbits live zero_lt_one small x with ⟨z,_,hs⟩|hs
  · rw [(hs.iteratedFDeriv ℝ n).self_of_nhds,iteratedFDeriv_comp_sub]; exact jets _
  · rw [(hs.iteratedFDeriv ℝ n).self_of_nhds];simpa using hB

theorem original (smooth:ContDiff ℝ ∞ f)(small:ρ+ρ<1)(live:support f⊆closedBall a ρ)(e:ℕ){B:ℝ}(hB:0≤B)
    (lower:∀x,‖f x‖≤B)(jets:∀x,‖iteratedFDeriv ℝ (WilsonSeparatedOriginalSlabFourierBudget.order J e) f x‖≤B):
    let F:=profile smooth small live
    Summable (fun k:J→ℤ=>‖mFourierCoeff F k‖*height k^e) ∧
    (∑'k:J→ℤ,‖mFourierCoeff F k‖*height k^e)≤B*WilsonSeparatedOriginalSlabFourierBudget.charge J e ∧
    ∀x:Room J,ρ+dist x a<1→HasSum (fun k:J→ℤ=>mFourierCoeff F k*mFourier k (wrap x)) (f x):=by
  let F:=profile smooth small live
  have eq:(fun x:Room J=>F (wrap x))=orbit a ρ 1 f:=funext (reads small live)
  have ready:ContDiff ℝ ∞ (fun x:Room J=>F (wrap x)):=eq.symm ▸ round smooth live zero_lt_one small
  have low:∀z,‖F z‖≤B:=by
    intro z; obtain ⟨x,rfl⟩:=onto z
    change ‖descended a ρ f (wrap x)‖≤B;rw [reads small live];unfold orbit;split
    · exact lower _
    · simpa using hB
  obtain ⟨fund,fee⟩:=WilsonSeparatedOriginalSlabFourierBudget.original F ready e hB low (fun x=>by rw [eq];exact bill small live _ hB jets x)
  refine ⟨fund,fee,?_⟩
  intro x hx
  have volume:Summable (mFourierCoeff F):=Summable.of_norm (fund.of_nonneg_of_le (fun _=>norm_nonneg _) (fun k=>le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (active k))))
  have center: orbit a ρ 1 f x=f x:=by
    have zero:flow 1 (0:Pitch J)=0:=by funext i;simp [flow]
    simpa only [zero,add_zero,sub_zero] using each live zero_lt_one (0:Pitch J) hx (by simpa only [zero,add_zero] using le_rfl (a:=dist x a))
  have out:=hasSum_mFourier_series_apply_of_summable volume (wrap x)
  simpa only [smul_eq_mul,show F (wrap x)=f x from (reads small live x).trans center] using out

end YM.Integration.WilsonSeparatedOriginalSlabCompactFourier
