import YM.Integration.WilsonOriginalGaussianFieldPhase
import YM.Integration.WilsonPositionProgramChronologicalReversal
import YM.FVAAlt2.Booth.Prices
import YM.Work.G05.Taylor

/-! Regrade a general analytic quiet action at a genuine clock, holding its angular argument fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedOriginalClockTaylor
open Filter Finset Function Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Assembly
open PertExtension.Series PertExtension.Series.Radial RegulatorIR.FVAAlt2 RegulatorIR
open RegulatorIR.FVAAlt2.Booth YM.Analysis
open scoped BigOperators Classical Topology ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C:UnitCost)
def ray (A:E)(t:ℝ):ℝ×E:=(C.enter t,t • A)
def radial (F:ℝ×E→ℝ)(r:ℕ)(A:E)(t:ℝ):ℝ:=
  ∑i∈range (r+1),(C.enter t)^i*Assembly.jet F (i+2) (1,(C.rating t)⁻¹ • A)

theorem expanded (F:ℝ×E→ℝ)(r:ℕ)(A:E)(first:∀x:E,Assembly.jet F 1 (1,x)=0)
    (t:ℝ)(rent:C.rating t≠0):
    Ribbon.fees C t * Work.G05.blockTaylor (r+2) F (ray C A t)=
      Ribbon.fees C t *F 0+t^2*radial C F r A t:=by
  let x:ℝ×E:=(1,(C.rating t)⁻¹ • A)
  have onRay:ray C A t=(C.enter t) • x:=by
    ext1
    · change C.enter t=C.enter t*1
      ring
    · change t • A=C.enter t • ((C.rating t)⁻¹ • A)
      rw [smul_smul,UnitCost.enter,mul_assoc,mul_inv_cancel₀ rent,mul_one]
  have paid:Ribbon.fees C t*(C.enter t)^2=t^2:=by
    unfold Ribbon.fees UnitCost.enter
    rw [mul_pow]
    field_simp
  let l:ℕ→ℝ:=fun i=>Assembly.jet F i x
  have bill:Work.G05.blockTaylor (r+2) F (ray C A t)=∑i∈range (r+2+1),(C.enter t)^i*l i:=by
    unfold Work.G05.blockTaylor
    rw [Finset.sum_apply,onRay]
    apply sum_congr rfl
    intro i _
    exact Tensor.homogeneous (Tensor.coeff F i 0) x (C.enter t)
  have zero:l 0=F 0:=by simp [l,Assembly.jet]
  have one:l 1=0:=first _
  let value:=radial C F r A t
  have header:Work.G05.blockTaylor (r+2) F (ray C A t)=F 0+(C.enter t)^2*value:=by
    rw [bill,sum_range_succ',sum_range_succ']
    simp [zero,one]
    rw [add_comm]
    congr 1
    change _ = (C.enter t)^2*(∑i∈range (r+1),(C.enter t)^i*l (i+2))
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  rw [header,mul_add,←mul_assoc,paid]

private theorem analyticTail (F:ℝ×E→ℝ)(r:ℕ)(smooth:ContDiffAt ℝ ω F 0):
    GradeAt (r+1) (F-Work.G05.blockTaylor r F):=by
  have poly:=Work.G05.blockTaylor_contDiff r F ⊤
  refine ⟨smooth.sub (Work.G05.blockTaylor_contDiff r F ω).contDiffAt,?_⟩
  intro k hk
  rw [iteratedFDeriv_sub_apply (smooth.of_le le_top) (poly.contDiffAt.of_le le_top),
    Work.G05.blockTaylor_jets (smooth.of_le le_top) k (by omega),sub_self]

/-- The budgeted finite jet commutes with the enrolled time change and the inverse quadratic fee. -/
theorem issued (F:ℝ×E→ℝ)(r:ℕ)(smooth:ContDiffAt ℝ ω F 0)
    (first:∀x:E,Assembly.jet F 1 (1,x)=0)(A:E){k:ℕ}(order:k≤r+2):
    Assembly.jet (fun t=>Ribbon.fees C t*F (ray C A t)) k 1=
      Assembly.jet (fun t=>Ribbon.fees C t*F 0+t^2*radial C F r A t) k 1:=by
  let f:=fun t=>Ribbon.fees C t*F (ray C A t)
  let p:=fun t=>Ribbon.fees C t*Work.G05.blockTaylor (r+2) F (ray C A t)
  have raySmooth:ContDiffAt ℝ ω (ray C A) 0:=C.here.prodMk (contDiffAt_id.smul contDiffAt_const)
  have origin:ray C A 0=0:=by simp [ray]
  have fee:ContDiffAt ℝ ω (Ribbon.fees C) 0:= (C.smooth.pow _).inv (by simp [C.origin])
  have clean:GradeAt (r+2+1) (f-p):=by
    have h:GradeAt (r+2+1) ((F-Work.G05.blockTaylor (r+2) F) ∘ ray C A):=
      (analyticTail F (r+2) smooth).coarse raySmooth origin
    have hfee : GradeAt 0 (Ribbon.fees C) := ⟨fee,fun _ hk=> (Nat.not_lt_zero _ hk).elim⟩
    have refined:=hfee.mul h
    rw [Nat.zero_add] at refined
    have he:f-p=Ribbon.fees C*((F-Work.G05.blockTaylor (r+2) F) ∘ ray C A):=by
      funext t
      simp only [f,p,Pi.sub_apply,Pi.mul_apply,comp_apply,mul_sub]
    rw [he]
    exact refined
  have hp:ContDiffAt ℝ ω p 0:=fee.mul ((Work.G05.blockTaylor_contDiff (r+2) F ω).contDiffAt.comp _ raySmooth)
  have hf:ContDiffAt ℝ ω f 0:=fee.mul ((origin.symm ▸ smooth).comp _ raySmooth)
  have difference:Assembly.jet (f-p) k (1:ℝ)=0:=by
    rw [Assembly.jet,clean.vanish k (by omega)]
    simp
  have yes:Assembly.jet f k (1:ℝ)=Assembly.jet p k 1:=by
    simpa only [Assembly.jet,iteratedFDeriv_sub_apply (hf.of_le le_top) (hp.of_le le_top),
      sub_apply,smul_sub,sub_eq_zero] using difference
  have same:p=ᶠ[𝓝 0]fun t=>Ribbon.fees C t*F 0+t^2*radial C F r A t:=
    C.bright.mono fun t h=>expanded C F r A first t h.ne'
  exact yes.trans (congrArg (fun z=>((k.factorial:ℝ)⁻¹) • z (fun _=>1))
    ((same.iteratedFDeriv ℝ k).eq_of_nhds))

end YM.Integration.WilsonCapturedOriginalClockTaylor
end
