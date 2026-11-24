import YM.Integration.WilsonPhysicalExteriorCoherentGrades

/-! The actual two-length finite Wilson point report on a coherent
bulk change. Only the physical ratio of the marked lengths survives;
all original mixed normalized readings and their common denominator stay. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorHomogeneousWord
open Finset PowerSeries Lattice PhysicalNext.Repeat.Legato
open MS MS.Land MS.Rake MS.Menus FVA2 FVAAlt2 Lobby Precision RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorRegisteredRows WilsonPhysicalExteriorRunningRows
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
variable {W:Type} [LinearOrder W] [Fintype W] {n:Side}
variable (R:Run G) (M:MS_Data G O) (Q:Prescription B)
local notation "PS" => PowerSeries ℂ
def fee (p:W→Label B) (y z:ℝ) (a:Array B (fun i=>(p i).h)) : PS :=
  ∏i:W, coordinates Q (p i).h z y z (Land.read (p i).item) (a i)

def word (p:W→Label B) (y z e:ℝ) (x:W→Site n) : PS :=
  ∑ a:Array B (fun i=>(p i).h),fee Q p y z a *
      reprice Q.team y z (newEra R.metals.O (basisR R) Q y (fun i=>owner (a i)) x e)

omit [LinearOrder W] in
private theorem priced (p:W→Label B) (e:ℝ) (eps:W→ℝ) :
    WilsonPhysicalExteriorSlotReference.engineering eps p * (e:ℂ)^wt p =
      WilsonPhysicalExteriorSlotReference.ratio eps e p := by
  rw [WilsonPhysicalExteriorSlotReference.ratio,WilsonPhysicalExteriorSlotReference.engineering,wt,
    ←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  refine prod_congr rfl (fun i _=>?_);rw [←mul_pow,div_eq_mul_inv,mul_comm]

omit [LinearOrder W] in
theorem omitted (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p:W→Label B) (y z:ℝ) (a:Array B (fun i=>(p i).h))
    (h:¬∀i:W,(a i).size=(p i).h) : fee Q p y z a=0 := by
  push Not at h
  obtain ⟨i,hi⟩:=h
  apply Finset.prod_eq_zero (mem_univ i)
  exact WilsonPhysicalExteriorCoherentGrades.original R M Q hG paid (p i).h (p i).item (a i)
    (lt_of_le_of_ne (MSFeeCoordinates.remaining _) hi) y z

/-- On arbitrary original sites, sides and outer lengths, the small
overall regulator spacing can now be removed from every nonzero row. -/
theorem measured (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p:W→Label B) (y z e:ℝ) (eps:W→ℝ) (x:W→Site n) (he:e≠0) (ok:∀i,eps i≠0) :
    WilsonPhysicalExteriorSlotReference.report R.metals.O (basisR R) Q p z (fun _=>z) eps x =
      C (WilsonPhysicalExteriorSlotReference.ratio eps e p)*word R Q p y z e x := by
  rw [WilsonPhysicalExteriorRunningRows.measured R.metals.O (basisR R) Q p (fun _=>z) eps y z e x ok he,
    word,mul_sum,mul_sum]
  apply sum_congr rfl;intro a _
  change C _*(fee Q p y z a*(C _*_))=C _*(fee Q p y z a*_)
  by_cases h:∀i:W,(a i).size=(p i).h
  · have eq:wt (fun i=>owner (a i))=wt p:=Finset.sum_congr rfl (fun i _=>h i)
    rw [eq,←priced p e eps,map_mul];ring
  · simp only [omitted R M Q hG paid p y z a h,zero_mul,mul_zero]

end YM.Integration.WilsonPhysicalExteriorHomogeneousWord
end
