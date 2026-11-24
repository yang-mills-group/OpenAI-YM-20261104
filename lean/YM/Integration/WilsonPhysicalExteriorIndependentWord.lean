import YM.Integration.WilsonPhysicalExteriorTransportedFields

/-! Independently normalized outer fields on the original joint finite
Wilson point. The subtraction left by using untransported fee series
is an explicit finite signed source on exactly the same measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorIndependentWord
open Finset PowerSeries Lattice PhysicalNext.Repeat.Legato
open MS MS.Land MS.Rake MS.Menus FVA2 FVAAlt2 Lobby FVAAlt2.Billing Precision
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorRegisteredRows WilsonPhysicalExteriorRunningRows WilsonPhysicalExteriorTransportedFields
open WilsonPhysicalExteriorFeeShift
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
variable {W:Type} [LinearOrder W] [Fintype W] {n:Side}
variable (R:Run G) (Q:Prescription B)
local notation "PS" => PowerSeries ℂ

def ticket (p:W→Label B) (v:W→ℝ) (z:ℝ) (a:Array B (fun i=>(p i).h)) : PS :=
  ∏i:W,reprice Q.team (v i) z (bore p Q (v i) i (a i))
def inserted (p:W→Label B) (v:W→ℝ) (z:ℝ) (x:W→Site n) : PS :=
  ∑a:Array B (fun i=>(p i).h),ticket Q p v z a *
      field R.metals.O (basisR R) Q z x (fun i=>(p i).h) a
def rate (p:W→Label B) (v:W→ℝ) (y z:ℝ) (a:Array B (fun i=>(p i).h)) : PS :=
  ∏i:W,column Q (p i) (v i) y z (a i)
def readings (p:W→Label B) (v:W→ℝ) (y z e:ℝ) (x:W→Site n) : PS :=
  ∑a:Array B (fun i=>(p i).h),rate Q p v y z a *
      reprice Q.team y z (newEra R.metals.O (basisR R) Q y (fun i=>owner (a i)) x e)

private theorem carried (d:W→ℕ) (y z:ℝ) (x:W→Site n) (a:Array B d) :
    reprice Q.team y z (WilsonPhysicalExteriorRegisteredRows.padded R.metals.O (basisR R) Q y x d a)=
      ∑ b:Array B d,(∏i:W,reprice Q.team y z (frame Q (d i) y (a i) (b i)))*
        field R.metals.O (basisR R) Q z x d b := by
  simp only [WilsonPhysicalExteriorRegisteredRows.padded,map_sum,map_mul,map_prod,field,
    WilsonPhysicalExteriorRunningRows.original]

private theorem rewritten (p:W→Label B) (v:W→ℝ) (y z:ℝ) (x:W→Site n) :
    inserted R Q p v z x=∑ a:Array B (fun i=>(p i).h),rate Q p v y z a*
      reprice Q.team y z (WilsonPhysicalExteriorRegisteredRows.padded R.metals.O (basisR R) Q y x (fun i=>(p i).h) a) := by
  let d:W→ℕ:=fun i=>(p i).h
  have hf (i:W) (b:Glyph B (d i)):reprice Q.team (v i) z (bore p Q (v i) i b)=
      ∑a:Glyph B (d i),column Q (p i) (v i) y z a*reprice Q.team y z (frame Q (d i) y a b) :=
    (bought Q (p i) (v i) y z b).symm
  unfold inserted ticket rate
  simp_rw [carried,hf,Fintype.prod_sum,Finset.sum_mul,Finset.prod_mul_distrib,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

omit [LinearOrder W] in
private theorem engineering (p:W→Label B) (e:ℝ) (eps:W→ℝ) :
    WilsonPhysicalExteriorSlotReference.engineering eps p * (e:ℂ)^wt p =
      WilsonPhysicalExteriorSlotReference.ratio eps e p := by
  rw [WilsonPhysicalExteriorSlotReference.ratio,WilsonPhysicalExteriorSlotReference.engineering,wt,
    ←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  refine prod_congr rfl (fun i _=>?_);rw [←mul_pow,div_eq_mul_inv,mul_comm]

private theorem normalize (u:W→Label B) (y z e:ℝ) (x:W→Site n) (he:e≠0) :
    reprice Q.team y z (prepare R.metals.O (basisR R) Q y u n x)=
      C ((e:ℂ)^wt u)*reprice Q.team y z (newEra R.metals.O (basisR R) Q y u x e) := by
  have fixed(a:ℂ):reprice Q.team y z (C a)=C a:=(reprice Q.team y z).commutes a
  rw [tot_cost R.metals.O (basisR R) Q y u x e he,map_mul,fixed,←mul_assoc,
    ←map_mul,←mul_pow,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr he),one_pow,map_one,one_mul]

theorem measured (M:MS_Data G O) (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p:W→Label B) (v eps:W→ℝ) (y z e:ℝ) (x:W→Site n) (he:e≠0) :
    C (WilsonPhysicalExteriorSlotReference.engineering eps p)*inserted R Q p v z x=
      C (WilsonPhysicalExteriorSlotReference.ratio eps e p)*readings R Q p v y z e x := by
  rw [rewritten R Q p v y z x,readings,mul_sum,mul_sum]
  apply sum_congr rfl;intro a _
  rw [sourced,normalize R Q _ y z e x he]
  by_cases h:∀i:W,(a i).size=(p i).h
  · have eq:wt (fun i=>owner (a i))=wt p:=Finset.sum_congr rfl (fun i _=>h i)
    rw [eq,←engineering p e eps,map_mul];ring
  · push Not at h
    obtain ⟨i,hi⟩:=h
    have van:rate Q p v y z a=0:=Finset.prod_eq_zero (mem_univ i)
      (WilsonPhysicalExteriorTransportedFields.lower Q R M hG paid (p i) (v i) y z (a i)
        (lt_of_le_of_ne (MSFeeCoordinates.remaining _) hi))
    simp only [van,zero_mul,mul_zero]

/-- The raw independently marked finite roster has a concrete signed
conversion term, with its original positions and Wilson vacuum. -/
theorem remainder (M:MS_Data G O) (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p:W→Label B) (v eps:W→ℝ) (y z e:ℝ) (x:W→Site n) (he:e≠0) (ok:∀i,eps i≠0) :
    WilsonPhysicalExteriorSlotReference.report R.metals.O (basisR R) Q p z v eps x-
      C (WilsonPhysicalExteriorSlotReference.ratio eps e p)*readings R Q p v y z e x=
      C (WilsonPhysicalExteriorSlotReference.engineering eps p)*
      ∑ a:Array B (fun i=>(p i).h),
        ((∏i:W,bore p Q (v i) i (a i))-ticket Q p v z a)*
          field R.metals.O (basisR R) Q z x (fun i=>(p i).h) a := by
  rw [←measured R Q M hG paid p v eps y z e x he,
    WilsonPhysicalExteriorSlotReference.factored R.metals.O (basisR R) Q p z v eps x ok,←mul_sub]
  congr 1
  unfold inserted WilsonPhysicalExteriorSlotReference.original
  rw [←sum_sub_distrib]
  apply sum_congr rfl;intro a _
  rw [sub_mul];rfl

end YM.Integration.WilsonPhysicalExteriorIndependentWord
end
