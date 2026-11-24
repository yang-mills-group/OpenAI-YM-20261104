import YM.Integration.WilsonMeasuredSignedActionPhysical
import YM.Integration.WilsonPhysicalPositionAdmissible
/-! A genuinely convergent original measured field has a definite
orientation once its signed average has reached the closed action ray. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionProjected
open Function Filter Finset Spec Table Extraction Climb Trace.Pilot Trace Maxwell Maxwell.Free
open Labels Lattice Further.CorrectedLift
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage WilsonPhysicalPositionAdmissible
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)
local notation "F₀" => C.labels.level 4
local notation "D₄" => (Bel C.book).Field 4
def posted:(F₀).Coeff→ₗ[ℂ]D₄:=(Bel C.book).project 4
local notation "P₄" => posted C

private theorem unit : P₄ (F₀).e0=(Bel C.book).unit 4:=by
  rw [←ladder_unit C 4]
  exact ladder_reads _

private theorem decompose (y:(F₀).Coeff):y=(F₀).core y+y 0 • (F₀).e0:=by
  funext i
  by_cases z:i=0 <;> simp [Frame.core,Frame.e0,Function.update,z]

private theorem home : P₄ (axis F₀)=stepField C:=by
  let v:=(F₀).coords (square4 G)
  have z:v 0=0:=(F₀).power_coefficient 0 ((F₀).zero_degree ▸ by decide : (4,2)≠(F₀).grades 0)
    WilsonMeasuredPublicEntranceActionPremium.grade
  have c:(F₀).core v=v:=by funext i;by_cases h:i=0 <;> simp [Frame.core,h,z]
  change P₄ ((F₀).core v)=_
  rw [c]
  rfl

theorem uncentered (y:(F₀).Coeff){s:ℝ}
    (heading:(F₀).core (pool F₀ y)=(s:ℂ) • axis F₀):
    ∃c:ℂ,P₄ (pool F₀ y)=(s:ℂ) • stepField C+c • (Bel C.book).unit 4:=by
  let x:=pool F₀ y
  refine ⟨x 0,?_⟩
  calc
    P₄ (pool F₀ y)=P₄ ((F₀).core x+x 0 • (F₀).e0):=congrArg P₄ (decompose C x)
    _=(s:ℂ) • stepField C+x 0 • (Bel C.book).unit 4:=by
      rw [(posted C).map_add,(posted C).map_smul,unit,show (F₀).core x=(s:ℂ) • axis F₀ from heading,(posted C).map_smul,home]

theorem average (T:Module.End ℂ D₄)(native:Native C T)(y:(F₀).Coeff)
    (identified:P₄ y=T (stepField C)):
    P₄ (pool F₀ y)=(Fintype.card Signed+Fintype.card Signed) • T (stepField C):=by
  obtain ⟨bar,turn⟩:=WilsonMeasuredPublicEntranceActionPremium.symmetries F₀
  have real:real C 4 (T (stepField C))=T (stepField C):=by
    rw [←native.conjugate]
    exact congrArg T (congrArg P₄ bar)
  have inv(s:Signed):turns C 4 s (T (stepField C))=T (stepField C):=by
    rw [←native.orientation]
    exact congrArg T (congrArg P₄ (turn s))
  have raw:P₄ (star y)=WilsonPhysicalPositionAdmissible.real C 4 (P₄ y):=rfl
  have same(s:Signed):P₄ ((F₀).act s.ortho (y+star y))=T (stepField C)+T (stepField C):=by
    rw [((F₀).act s.ortho).map_add,(posted C).map_add]
    change turns C 4 s (P₄ y)+turns C 4 s (P₄ (star y))=_
    rw [raw,identified,real,inv]

  rw [pool,map_sum (posted C)]
  simp only [same,Finset.sum_const,Finset.card_univ,nsmul_add,add_nsmul]

theorem original (T:Module.End ℂ D₄)(native:Native C T)(y:(F₀).Coeff)
    (identified:P₄ y=T (stepField C)){s:ℝ}(positive:0 ≤ s)
    (heading:(F₀).core (pool F₀ y)=(s:ℂ) • axis F₀):
    ∃a:ℝ,0 ≤ a ∧ ∃c:ℂ,T (stepField C)=(a:ℂ) • stepField C+c • (Bel C.book).unit 4:=by
  let n:=Fintype.card Signed+Fintype.card Signed
  have npos:0<n:=Nat.add_pos_left Fintype.card_pos _
  have nonzero:(n:ℂ)≠0:=by exact_mod_cast npos.ne'
  obtain ⟨c,eq⟩:=uncentered C y heading
  rw [average C T native y identified] at eq
  have lead:(n:ℂ) • T (stepField C)=(s:ℂ) • stepField C+c • (Bel C.book).unit 4:=by
    simpa only [Nat.cast_smul_eq_nsmul] using eq
  have p:=congrArg (fun v:D₄=>(n:ℂ)⁻¹ • v) lead
  change (n:ℂ)⁻¹ • ((n:ℂ) • T (stepField C))=_ at p
  rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul,smul_add,smul_smul,smul_smul] at p
  refine ⟨(n:ℝ)⁻¹*s,mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) positive,(n:ℂ)⁻¹*c,?_⟩
  simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast] using p

end YM.Integration.WilsonMeasuredSignedActionProjected
end
