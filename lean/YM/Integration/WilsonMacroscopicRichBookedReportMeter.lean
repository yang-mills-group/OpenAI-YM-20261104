import YM.Integration.WilsonMacroscopicRichChildRegistration

/-! One linear meter for all the actually booked fields at a single original
cutoff and filing date. Its values on that domain are the literal topReport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichBookedReportMeter
open Function MeasureTheory Lattice Wilson RG Source Trace.Physical.GermGraph RG16.Literal
open scoped Topology BigOperators Classical
variable {G : Gauge} (C : Family G) (H : C.Makes) {d N p b : ℕ}
variable (door:Opened C d b p) (live:b≤N)
local notation "X"=>Config G (C.side N p)
local notation "R!"=>topReport C N p d H b door live
local notation "B!"=>fun f=>Booked C N p d f b live

theorem add (f k:C(X,ℂ)) (hf:B! f) (hk:B! k) :
    B! (f+k:C(X,ℂ)) ∧ R! (f+k:C(X,ℂ))=R! f+R! k := by
  let e:Fin 2→C(X,ℂ):=![f,k]
  have booked(i:Fin 2):B! (e i):=by fin_cases i;exact hf;exact hk
  have all:=IntrinsicProductLinearity.booked_sum C N p d b H door live (fun _:Fin 2=>(1:ℂ))
    (fun i=>(e i:X→ℂ)) (fun i=>(e i).continuous) booked
  simpa [e,Fin.sum_univ_two] using all

theorem smul (t:ℂ)(f:C(X,ℂ))(hf:B! f) :
    B! (t•f:C(X,ℂ)) ∧ R! (t•f:C(X,ℂ))=t•R! f := by
  have all:=IntrinsicProductLinearity.booked_sum C N p d b H door live (fun _:Fin 1=>t)
    (fun _=>(f:X→ℂ)) (fun _=>f.continuous) (fun _=>hf)
  simpa using all

def sector : Submodule ℂ C(X,ℂ) where
  carrier:={f|B! f}
  zero_mem':=by
    have sale:=(WilsonMacroscopicRichChildRegistration.issued C H (0:C.label d) door live).1
    have zero:(C.O N p (0:C.label d) 0:X→ℂ)=0:=((C.linearO N p d 0).mk' _).map_zero
    rw [zero] at sale;exact sale
  add_mem' := fun {f k} hf hk=>(add C H door live f k hf hk).1
  smul_mem' := fun t {f} hf=>(smul C H door live t f hf).1

def filed : sector C H door live →ₗ[ℂ] C.label d where
  toFun f:=R! (f.1:X→ℂ)
  map_add' f k:=(add C H door live f.1 k.1 f.2 k.2).2
  map_smul' t f:=(smul C H door live t f.1 f.2).2

theorem original : ∃ L:C(X,ℂ)→ₗ[ℂ]C.label d,
    ∀ f:C(X,ℂ), B! f → L f=R! f :=by
  obtain ⟨L,agrees⟩:=(filed C H door live).exists_extend
  refine ⟨L,fun f earned=>?_⟩
  exact LinearMap.congr_fun agrees (⟨f,earned⟩:sector C H door live)

end YM.Integration.WilsonMacroscopicRichBookedReportMeter
