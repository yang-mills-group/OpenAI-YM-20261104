import YM.Integration.WilsonReceivedDepositedOrbitalThermals

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalIntegral
open Finset Marker Multi MeasureTheory Filter Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open WilsonReceivedDepositedOrbitalSlice
open scoped Classical BigOperators
variable {V W:Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W]
  {A:Census V}{J:Census W}{E:Type}[MeasurableSpace E]

omit [Fintype V] [Fintype W] in
theorem coefficients (F:Poly A →ₐ[ℂ] Poly J)(x:Poly A)(s:J.Mode):
    (F x).part s=∑a,x.part a*(F (Poly.send a 1)).part s:=by
  have rows(a:A.Mode):Poly.send a (x.part a)=(x.part a) • Poly.send a 1:=by
    apply Marker.Poly.ext
    intro b
    by_cases eqn:b=a <;> simp [eqn]
  calc
    (F x).part s=(F (∑a,Poly.send a (x.part a))).part s:=by rw [Poly.studs]
    _=_:=by simp only [rows,map_sum,map_smul,Poly.part_sum,Poly.part_smul]

def take (μ:Measure E)(source:E→Poly A):Poly A:=
  Poly.inject fun s=>∫z,(source z).part s ∂μ

omit [Fintype V] [Fintype W] in
theorem integrated (F:Poly A →ₐ[ℂ] Poly J)(μ:Measure E)(source:E→Poly A)
    (earned:∀s,Integrable (fun z=>(source z).part s) μ):
    F (take μ source)=take μ (fun z=>F (source z)):=by
  apply Marker.Poly.ext
  intro s
  rw [coefficients]
  change (∑a,(∫z,(source z).part a ∂μ)*(F (Poly.send a 1)).part s)=
    ∫z,(F (source z)).part s ∂μ
  simp_rw [coefficients F (source _) s,integral_finsetSum _ (fun a _=>(earned a).mul_const _),integral_mul_const]

theorem retest {Z:Type}[Fintype Z][DecidableEq Z]{r:ℕ}
    (J:Census V)(name:Z→Hot J)(μ:Measure E)
    (temporary:E→Grade (Stock.census Z) r)(physical:E→Grade J r)
    (on_fields:∀z,(hom (WilsonReceivedDepositedAlias.fold J name) r) (temporary z)=physical z)
    (earned:∀s,Integrable (fun z=>(temporary z).part s) μ)
    (unit:UnitLeading (take μ temporary))(j:ℕ):
    let φ:=WilsonReceivedDepositedAlias.fold J name
    Order.observe J r (Order.ratio (take μ physical)) j=φ (Order.observe (Stock.census Z) r (Order.ratio (take μ temporary)) j) ∧
    Order.observe J r (Order.logMarked (take μ physical)) j=φ (Order.observe (Stock.census Z) r (Order.logMarked (take μ temporary)) j):=by
  intro φ
  obtain ⟨normalized,marked⟩:=WilsonReceivedDepositedOrbitalThermals.original J name (take μ temporary) unit j
  have joint:hom φ r (take μ temporary)=take μ physical:=by
    rw [integrated _ μ temporary earned,funext on_fields]
  exact ⟨joint ▸ normalized,joint ▸ marked⟩

end YM.Integration.WilsonReceivedDepositedOrbitalIntegral
end
