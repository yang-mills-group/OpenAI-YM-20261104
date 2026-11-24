import YM.Integration.WilsonMatrixOriginalGermReturnParts

/-! The earlier regular pair has a uniform pointwise bound on the whole
Wilson configuration space, including coincident addresses. Its signed
two-mean response therefore spends the first absolute spring moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermReturnRegular
open Finset MeasureTheory Lattice Wilson RG Source MergeProof OPE.Therm PhysicalNext.Repeat.Legato
open Trace.Physical.GermGraph Next.Rank.Price Next.UVStress WilsonInheritedRegisteredField
open WilsonRegisteredRegularQuota WilsonMatrixOriginalGermReturnParts Push.GridApprox FVA2
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {m N p:ℕ}
local notation "β"=>R.family.path.levels.clock.hatBeta

def panel (live:m≤N) (v:Fin 2→R.family.label 4) (φ:Test 2) (V:Config G (R.family.side m p)):ℂ:=
  let μ:=scene R.family.path N p m
  let arm (x:Fin 2→Site (R.family.side N p)) (i:Fin 2):=regular R.makes live (v i) ((R.family.S.toDepth live p).parent (x i))
  ∑x:Fin 2→Site (R.family.side N p),WilsonExternalMeshMass.charge R.family φ x*proper μ (arm x 0) (arm x 1) V

def debit (live:m≤N) (v:Fin 2→R.family.label 4) (φ:Test 2) (W:Config G (R.family.side m p)→ℂ):ℂ:=
  ∫V,panel R live v φ V*W V ∂scene R.family.path N p m

theorem cap (age:R.family.ref 4 ≤ m) (live:m≤N) (cheap:stock R.family m≤β m) (e:ℕ)
    (w:R.family.label 4) (fee:quota R.family 4 m N p w≤R.family.S.a m^4*β m^e) (o:Site (R.family.side m p))
    (V:Config G (R.family.side m p)):
    ‖regular R.makes live w o V‖≤3*β m^(e+1):=by
  have b:0≤β m:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have a:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos _) 4
  have iq:=mul_le_mul_of_nonneg_left fee (inv_pos.mpr a).le
  rw [←mul_assoc,inv_mul_cancel₀ a.ne',one_mul] at iq
  have stock0:0 ≤ stock R.family m:=zero_le_one.trans (R.family.path.levels.params m).columns_ge
  calc
    _ ≤ 3*stock R.family m*((R.family.S.a m^4)⁻¹*quota R.family 4 m N p w):=WilsonRegisteredRegularQuota.original R.makes live age w o V
    _ ≤ 3*stock R.family m*β m^e:=mul_le_mul_of_nonneg_left iq (mul_nonneg (by norm_num) stock0)
    _ ≤ 3*β m*β m^e:=by gcongr
    _ = _ := by rw [pow_succ];ring

theorem charged (age:R.family.ref 4 ≤ m) (live:m≤N) (cheap:stock R.family m≤β m) (e:ℕ)
    (v:Fin 2→R.family.label 4) (fee:∀i,quota R.family 4 m N p (v i)≤R.family.S.a m^4*β m^e)
    (φ:Test 2) (W:Config G (R.family.side m p)→ℂ) (hw:Envelope W):
    ‖debit R live v φ W‖ ≤
      (54*(∑x:Fin 2→Site (R.family.side N p),‖WilsonExternalMeshMass.charge R.family φ x‖)*β m^(2*(e+1)))*
      (∫V,‖W V‖ ∂scene R.family.path N p m):=by
  let μ:=scene R.family.path N p m
  letI:IsProbabilityMeasure μ:=OPE.Therm.probability R.makes.wilson live
  let c:=3*β m^(e+1)
  have bp:0≤β m:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have cp:0≤c:=mul_nonneg (by norm_num) (pow_nonneg bp _)
  let arm (x:Fin 2→Site (R.family.side N p)) (i:Fin 2):Config G (R.family.path.S.side m p)→ℂ:=
    regular R.makes live (v i) ((R.family.S.toDepth live p).parent (x i))
  let a:=fun x:Fin 2→Site (R.family.side N p)=>WilsonExternalMeshMass.charge R.family φ x
  let M:=54*(∑x,‖a x‖)*β m^(2*(e+1))
  have bound (V:Config G (R.family.path.S.side m p)):‖panel R (p:=p) live v φ V‖≤M:=by
    change ‖∑x,a x*proper μ (arm x 0) (arm x 1) V‖≤M
    calc
      _ ≤ ∑x,‖a x*proper μ (arm x 0) (arm x 1) V‖:=norm_sum_le ..
      _ ≤ ∑x,‖a x‖*(6*(c*c)):=by
        apply sum_le_sum;intro x _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact bounded μ cp (cap R age live cheap e (v 0) (fee 0) _) (cap R age live cheap e (v 1) (fee 1) _) V
      _ = _ :=by rw [←sum_mul];dsimp [M,c];rw [Nat.mul_comm 2 (e+1),pow_mul];ring
  calc
    _ ≤ ∫V,M*‖W V‖ ∂μ:=by
      exact norm_integral_le_of_norm_le ((hw.integrableC μ).norm.const_mul M)
        (Filter.Eventually.of_forall fun V=>(norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (bound V) (norm_nonneg _)))
    _ = _ :=integral_const_mul _ _

end YM.Integration.WilsonMatrixOriginalGermReturnRegular
