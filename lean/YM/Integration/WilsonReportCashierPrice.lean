import YM.Integration.WilsonReportRegulatedSmear
import YM.RG17.Apron

/-! At the genuine vacuum test, the mass of all fine lattice smear weights
is uniformly paid before regulator, period, test and internal order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCashierPrice
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open OPE OPE.Orbits RG17 Table WilsonReportFineSmear
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

/-- The discrete test weight on the entire true finest regulator. No norm of
the gauge-observable numerator enters this estimate. -/
theorem purchased (F : Spec.Final C f S) (T : Test 1) {n : ℕ} {K : Set (Points (n+1))}
    (hK : IsCompact K) (hc : K⊆conf _) :
    ∃ c : ℝ,0≤c ∧ ∀ᶠ r in RG17.home,
    ∀ ψ : Test (n+1),tsupport ψ⊆K → ∀ b : ℝ,Demand 0 ψ b →
    ∀ k N p : ℕ, k≤N → C.S.a N≤r →
    ∑ y : Fin (n+1)→Site (C.side N p),‖weight C (RG17.shape (RG17.cashier F T) r ψ) y‖ ≤ c*b := by
  obtain ⟨A,B,hA,hB,full⟩ := RG17.addressCosts F T K hK hc
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  filter_upwards [full] with r bill ψ compact b paid k N p hk small
  obtain ⟨origin,family⟩ := bill ψ compact 0 b paid k N p hk small
  let op := RG17.shape (RG17.cashier F T) r ψ
  let Y := Fin (n+1)→Site (C.side N p)
  let z (y : Y) := (C.S.toDepth hk p).parent (y 0)
  let jobs : Finset Y := univ.filter (fun y => Order.cells C N p y∈RG17.gathersIn C F T K r)
  let U (a : Site (C.side k p)) := RG17.yarns C F T K k N p hk a r
  let V := RG17.spools C F T K k N p hk r
  let w (y : Y) := ‖weight C op y‖
  let d := 4*(n+1)
  have actual (y : Y) : w y=C.S.a N^d*‖op (Order.cells C N p y)‖ := by
    change ‖(C.S.a N:ℂ)^d*op (Order.cells C N p y)‖=_
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos N).le]
  have alive : ∀ y : Y,y∈jobs → z y∈V := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _,y,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2,rfl⟩⟩
  have group := sum_fiberwise_of_maps_to (s:=jobs) (t:=V) (g:=z) alive w
  have clip : (∑ y∈jobs,w y)=∑ y,w y := by
    apply sum_subset (subset_univ _)
    intro y _ missed
    have outside : Order.cells C N p y∉RG17.gathersIn C F T K r :=
      fun h => missed (mem_filter.mpr ⟨mem_univ _,h⟩)
    have zero : op (Order.cells C N p y)=0 := image_eq_zero_of_notMem_tsupport
      (fun hz => outside (RG17.gathered C F T K hK compact hz))
    rw [actual,zero,norm_zero,mul_zero]
  have same (i : Site (C.side k p)) : jobs.filter (fun y=>z y=i)=U i := by
    ext y
    simp only [jobs,U,RG17.yarns,Finset.mem_filter,Finset.mem_univ,true_and,z]
  have each (i) : (∑ y∈U i,w y) ≤ B*C.S.a k^4*b := by
    calc
      _ = C.S.a N^d*(∑ y∈U i,‖op (Order.cells C N p y)‖) := by
        rw [mul_sum]; exact sum_congr rfl (fun y _ => actual y)
      _ ≤ _ := family i
  change (∑ y,w y)≤_
  rw [←clip,←group]
  calc
    _ = ∑ i∈V,∑ y∈U i,w y := sum_congr rfl (fun i _ => by rw [same])
    _ ≤ ∑ _i∈V,B*C.S.a k^4*b := sum_le_sum (fun i _ => each i)
    _ = (C.S.a k^4*(V.card:ℝ))*(B*b) := by rw [sum_const,nsmul_eq_mul]; ring
    _ ≤ A*(B*b) := mul_le_mul_of_nonneg_right origin (mul_nonneg hB paid.nonneg)
    _ = _ := (mul_assoc ..).symm

end YM.Integration.WilsonReportCashierPrice
end

