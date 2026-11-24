import YM.Integration.WilsonMeasuredMarkedPrimary

/-! Separate the original one-date projection cost from the signed residual and
its one source radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPrimaryTariff
open Wilson Lattice RG Source Labels Push.Local

def cost {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (p:BudgetPoint) (A:Hol G)
    (S:SectionData F) (o:Site n) (w:ℝ) : ℝ :=
  let f:ℝ:=p.order.factorial
  let z:=factor A S p.supportExponent w * f
  8*max (f+z+p.mass (S.footprint o) (w*z)) (2*(1+z))

def allowance {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (p:BudgetPoint) (A:Hol G)
    (S:SectionData F) (o:Site n) (w:ℝ) : ℝ :=
  let f:ℝ:=p.order.factorial
  let z:=factor A S p.supportExponent w * f
  4*(f+z+p.mass (S.footprint o) (w*z))

theorem funds {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (p:BudgetPoint) (A:Hol G)
    (S:SectionData F) (o:Site n) (w:ℝ) {θ:ℝ} (radius:0<θ) (r:ℝ) :
    let f:ℝ:=p.order.factorial
    let z:=factor A S p.supportExponent w * f
    let s:=z*(4*r)
    let c:=f*(4*r)+s+θ*p.mass (S.footprint o) (w*(s/θ))
    c/θ = allowance p A S o w*r/θ := by
  dsimp only [allowance,BudgetPoint.mass]
  field_simp [radius.ne']

theorem cash {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (p:BudgetPoint) (A:Hol G)
    (S:SectionData F) (o:Site n) (w:ℝ) {θ r:ℝ} (radius:0<θ) (positive:0≤r) :
    let f:ℝ:=p.order.factorial
    let z:=factor A S p.supportExponent w * f
    let s:=z*(4*r)
    let c:=f*(4*r)+s+θ*p.mass (S.footprint o) (w*(s/θ))
    2*max (c/θ) (2*(4*r+s)/θ) = cost p A S o w*r/θ := by
  intro f z s c
  have one:c/θ=(f+z+p.mass (S.footprint o) (w*z))*(4*r/θ):=by
    dsimp only [c,s,BudgetPoint.mass]
    field_simp [radius.ne']
  have two:2*(4*r+s)/θ=(2*(1+z))*(4*r/θ):=by dsimp [s];ring
  rw [one,two,← max_mul_of_nonneg _ _ (div_nonneg (mul_nonneg (by norm_num) positive) radius.le)]
  change 2*(max _ _*(4*r/θ))=8*(max _ _)*r/θ
  ring

end YM.Integration.WilsonMeasuredPrimaryTariff
end

