import YM.Integration.WilsonCapturedOriginalClockTaylor
import YM.Integration.WilsonCapturedOriginalClockUntiming
import YM.Integration.WilsonCapturedRootedAngularSlots

/-! The actual submitted occupied field with its own numerical clock and
the exact original source power. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedOccupiedClockTaylor
open Filter Finset Function Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Assembly
open Comparison.RG02.Moving.Path PertExtension.Series PertExtension.Series.Radial
open RegulatorIR.FVAAlt2 RegulatorIR RegulatorIR.FVAAlt2.Booth YM.Analysis
open WilsonCapturedOriginalClockTaylor
open private affine from YM.Integration.WilsonCapturedOriginalClockUntiming
open scoped BigOperators Classical Topology ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def layers (F:ℝ×E→ℂ):Display E:=fun i A=>Assembly.jet F i (1,A)
def reported (C:UnitCost) (power q:ℕ) (F:ℝ×E→ℂ) (A:E):ℂ:=
  motion (fun t:ℝ=>((C.rating t)^power)⁻¹ • F (ray C A t)) q

theorem grades (F:ℝ×E→ℂ)(smooth:ContDiffAt ℝ ω F 0)(K:ℕ):
    Charge K (fun i:ℕ=>(i:ℤ)) (layers F):=by
  intro i _
  let U:E→L[ℝ] ℝ×E:=ContinuousLinearMap.inr ..
  have row:=affine (Adjacent.levelJet smooth i) U ((1:ℝ),(0:E))
  change Valence.Level (i:ℤ) (fun x:E=>Assembly.jet F i (1,x))
  simpa only [U,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using row

private theorem tail (F:ℝ×E→ℂ)(q:ℕ)(smooth:ContDiffAt ℝ ω F 0):
    GradeAt (q+1) (F-Work.G05.blockTaylor q F):=by
  refine ⟨smooth.sub (Work.G05.blockTaylor_contDiff q F ω).contDiffAt,?_⟩
  intro i hi
  rw [iteratedFDeriv_sub_apply (smooth.of_le le_top) ((Work.G05.blockTaylor_contDiff q F ⊤).contDiffAt.of_le le_top),
    Work.G05.blockTaylor_jets (smooth.of_le le_top) i (by omega),sub_self]

theorem original (C:UnitCost) (power q:ℕ) (F:ℝ×E→ℂ) (smooth:ContDiffAt ℝ ω F 0) (A:E):
    reported C power q F A=born (layers F) C (-(power:ℤ)) q q A:=by
  let fee:=fun t:ℝ=>((C.rating t)^power)⁻¹
  let f:=fun t:ℝ=>fee t • F (ray C A t)
  let g:=fun t:ℝ=>fee t • Work.G05.blockTaylor q F (ray C A t)
  have wages:ContDiffAt ℝ ω fee 0:=(C.smooth.pow _).inv (by simp [C.origin])
  have plotted:ContDiffAt ℝ ω (ray C A) 0:=C.here.prodMk (contDiffAt_id.smul contDiffAt_const)
  have home:ray C A 0=0:=by simp [ray]
  have hf:ContDiffAt ℝ ω f 0:=wages.smul ((home.symm ▸ smooth).comp _ plotted)
  have hg:ContDiffAt ℝ ω g 0:=wages.smul ((Work.G05.blockTaylor_contDiff q F ω).contDiffAt.comp _ plotted)
  have quiet:GradeAt 0 fee:=⟨wages,fun _ h=>(Nat.not_lt_zero _ h).elim⟩
  have rest:=quiet.scale ((tail F q smooth).coarse plotted home)
  rw [Nat.zero_add] at rest
  have diff:f-g=(fun t=>fee t • ((F-Work.G05.blockTaylor q F) ∘ ray C A) t):=by
    funext t;simp only [f,g,Pi.sub_apply,comp_apply,smul_sub]
  have small:Assembly.jet (f-g) q (1:ℝ)=0:=diff ▸ rest.jet_z 1 (by omega)
  have same:Assembly.jet f q (1:ℝ)=Assembly.jet g q 1:=by
    simpa only [Assembly.jet,iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top),
      sub_apply,smul_sub,sub_eq_zero] using small
  have expand:g=ᶠ[𝓝 0](fun t=>ages (layers F) (-(power:ℤ)) q t (C.rating t) A):=by
    apply C.bright.mono
    intro t ht
    let x:ℝ×E:=(1,(C.rating t)⁻¹ • A)
    have scaled:ray C A t=C.enter t • x:=by
      ext1
      · change C.enter t=C.enter t*1;ring
      · change t • A=C.enter t • ((C.rating t)⁻¹ • A)
        rw [smul_smul,UnitCost.enter,mul_assoc,mul_inv_cancel₀ ht.ne',mul_one]
    change fee t • Work.G05.blockTaylor q F (ray C A t)=((↑((C.rating t)^(-(power:ℤ))):ℂ))*
      cover (layers F) q (t*C.rating t) ((C.rating t)⁻¹ • A)
    unfold Work.G05.blockTaylor
    rw [Finset.sum_apply,scaled,cover]
    simp only [Tensor.homogeneous,zpow_neg,zpow_natCast,Complex.real_smul,Complex.ofReal_mul,
      Complex.ofReal_pow,UnitCost.enter,layers,Assembly.jet]
    rfl
  exact same.trans (congrArg (fun z=>((q.factorial:ℝ)⁻¹) • z (fun _=>1))
    ((expand.iteratedFDeriv ℝ q).eq_of_nhds))

end YM.Integration.WilsonCapturedOccupiedClockTaylor
