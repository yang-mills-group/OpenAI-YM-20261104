import YM.Integration.WilsonThermometerUnitFilingCoverChart

/-! Embed the local cover angular coordinates on a genuine multiple of the filed torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverPort
open Function Lattice Gauge RG RegulatorIR Exterior Diagram Budget Budget.Packet Binding Prim Profiles Halo
open Stationary QuadraticLocal WilsonThermometerUnitFilingCoverChart WilsonEmittedRootedJetWage
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{N:Side}{S:Finset Cover}(sites:Centered N S)(p:Site N)

def branch (G:Gauge): ↥(WilsonThermometerUnitFilingCoverChart.patch G S) ↪ Site N × Loc G 1 where
  toFun j:=(wrap N j.1.1.1+p,coord j.1.1.2,j.1.2)
  inj' :=by
    rintro ⟨⟨⟨x,d⟩,c⟩,hx⟩ ⟨⟨⟨y,e⟩,f⟩,hy⟩ H
    change (wrap N x+p,coord d,c)=(wrap N y+p,coord e,f) at H
    have both:=Prod.mk.inj H
    have sites_x:x∈S:=(Finset.mem_product.mp (Finset.mem_product.mp hx).1).1
    have sites_y:y∈S:=(Finset.mem_product.mp (Finset.mem_product.mp hy).1).1
    have same : x=y:=wrap_injOn N (sites x sites_x) (sites y sites_y) (add_right_cancel both.1)
    obtain ⟨dir,col⟩:=Prod.mk.inj both.2
    have dirs:d=e:=axisEquiv.injective dir
    exact Subtype.ext (by simp [same,dirs,col])

def put (G:Gauge):Figure (↥(WilsonThermometerUnitFilingCoverChart.patch G S)) →L[ℝ] Joint G N:=
  (ContinuousLinearMap.id ℝ ℝ).prodMap
    (edgeColor.toContinuousLinearMap.comp (liftFill (branch sites p G)).toContinuousLinearMap)

theorem ray (i:Option (↥(WilsonThermometerUnitFilingCoverChart.patch G S))):
    put sites p G (WilsonThermometerUnitFilingJointTensor.axis i)=
      peg G N (i.map (branch sites p G)):=by
  cases i with
  | none => change ((1:ℝ),edgeColor ((liftFill _) (0:_)))=_
            rw [map_zero,map_zero];rfl
  | some i =>
    change ((0:ℝ),edgeColor (fill (branch sites p G) (Pi.single i 1)))=
      (0,edgeColor (WilsonOriginalLinkedAngularPage.ray G (branch sites p G i)))
    congr 2
    funext q
    by_cases h:q∈Set.range (branch sites p G)
    · obtain ⟨j,rfl⟩:=h
      change dilute (branch sites p G) (Pi.single i 1) (branch sites p G j)=
        (if branch sites p G j=branch sites p G i then 1 else 0)
      rw [dilute_here]
      by_cases same:j=i
      · subst j;simp
      rw [if_neg (fun e=>same ((branch sites p G).injective e)),Pi.single_eq_of_ne same]
    have hm:q≠branch sites p G i:=by intro eq;exact h ⟨i,eq.symm⟩
    simp [fill,dilute_miss _ _ _ h,WilsonOriginalLinkedAngularPage.ray,hm]

theorem field (B:Portrait G)(inside:∀ t,LocalOn S (B t))(z:Figure (↥(WilsonThermometerUnitFilingCoverChart.patch G S))):
    script S B z = B (put sites p G z).1
      (expandAt p (increment 1 (put sites p G z).2)):=by
  apply inside z.1
  intro edge here _
  change G.lieExp (timber G (fill (placeFin (WilsonThermometerUnitFilingCoverChart.patch G S)) z.2) edge)=G.lieExp _ * 1
  rw [mul_one]
  apply congr_arg G.lieExp
  ext1 c
  let i:↥(WilsonThermometerUnitFilingCoverChart.patch G S):=⟨(edge,c),Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨here,Finset.mem_univ _⟩,Finset.mem_univ _⟩⟩
  change dilute (placeFin (WilsonThermometerUnitFilingCoverChart.patch G S)) z.2 (placeFin _ i)=
    dilute (branch sites p G) z.2 (branch sites p G i)
  rw [dilute_here,dilute_here]

end YM.Integration.WilsonThermometerUnitFilingCoverPort
