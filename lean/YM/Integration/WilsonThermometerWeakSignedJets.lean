import YM.Integration.WilsonThermometerWeakJetRecovery

/-! Signed fixed-order tests on the continuum difference recover uniform
spatial derivatives. The external test height D is chosen for this one
coefficient order. The larger independent packet is restored at the end. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSignedJets
open Spec Filter Set Next.UVStress WilsonThermometerWeakValueRecovery
open scoped Classical Topology ContDiff
variable {A:Type*}{n:ℕ}{l:Filter A}{U:Set (Points n)} (openU:IsOpen U)
    (clear:U⊆conf n) (g:A→ℝ) (j p D:ℕ)
    (limit:Tendsto g l (𝓝 0)) (positive:∀ᶠr in l,0<g r)

def high (j p:ℕ):ℕ:=2^j*(p+1)

include openU clear limit positive in
theorem measured (F:A→Points n→ℂ) (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)
    (signed:WilsonThermometerWeakValueRecovery.Signed l U F g (high j p+1) D)
    (funded:Bounded l U F ((4*n+D+1)*high j p+1))
    (short:∀a,2≤a→a≤j+1→Bounded l U F a):Price l U F g (p+1) j:=
  WilsonThermometerWeakJetRecovery.original openU F g j (p+1) (Nat.succ_pos p) limit positive smooth
    (WilsonThermometerWeakValueRecovery.original openU clear F g (high j p) D limit positive smooth signed funded) short

include openU limit positive in
theorem restore (T P Q:A→Points n→ℂ) (trueSmooth:∀ᶠr in l,ContDiffOn ℝ ∞ (T r) U)
    (topSmooth:∀ᶠr in l,ContDiffOn ℝ ∞ (Q r) U)(printedSmooth:∀ᶠr in l,ContDiffOn ℝ ∞ (P r) U)
    (top:Price l U (fun r=>T r-Q r) g (p+1) j)(tail:Price l U (fun r=>Q r-P r) g (p+1) j):
    ∀K,IsCompact K→K⊆U→∀ε:ℝ,0<ε→∀ᶠr in l,∀x∈K,
      ‖iteratedFDeriv ℝ j (T r) x-iteratedFDeriv ℝ j (P r) x‖≤ε*g r^p:=by
  intro K compact inside ε ep
  obtain ⟨A,An,a⟩:=top K compact inside
  obtain ⟨B,Bn,b⟩:=tail K compact inside
  have floor:∀ᶠr in l,(A+B)*g r<ε:=
    (show Tendsto (fun r=>(A+B)*g r) l (𝓝 0) by simpa using tendsto_const_nhds.mul limit).eventually_lt_const ep
  filter_upwards [a,b,positive,floor,trueSmooth,topSmooth,printedSmooth] with r first last pos low t q u x hx
  have jt:ContDiffAt ℝ j (T r) x:=((t x (inside hx)).contDiffAt (openU.mem_nhds (inside hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have jq:ContDiffAt ℝ j (Q r) x:=((q x (inside hx)).contDiffAt (openU.mem_nhds (inside hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have ju:ContDiffAt ℝ j (P r) x:=((u x (inside hx)).contDiffAt (openU.mem_nhds (inside hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have one:=first x hx;have two:=last x hx
  rw [iteratedFDeriv_sub_apply jt jq] at one
  rw [iteratedFDeriv_sub_apply jq ju] at two
  calc _≤‖iteratedFDeriv ℝ j (T r) x-iteratedFDeriv ℝ j (Q r) x‖+
         ‖iteratedFDeriv ℝ j (Q r) x-iteratedFDeriv ℝ j (P r) x‖:=norm_sub_le_norm_sub_add_norm_sub ..
       _≤A*g r^(p+1)+B*g r^(p+1):=add_le_add one two
       _=(A+B)*g r*g r^p:=by rw [pow_succ];ring
       _≤_:=mul_le_mul_of_nonneg_right low.le (pow_nonneg pos.le _)

end YM.Integration.WilsonThermometerWeakSignedJets
end
