import YM.Integration.FVA1Physical.Sources.Round2.FieldReceipt
import YM.MSbar.Ballet.Present

/-! A single Ballet invoice for the original vacuum and both components of every physical mixed insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open YM.MSbar YM.MSbar.Ballet RGComparison.Core16.Spool
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree YM.Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Heath Stock -- Hunger Horizon conflict. 
variable (O:ChartRatio G)(K:MapPrices)(p s m:ℕ)(j i:ℕ)(H H':Stage)(P:Patch)(X:KernelChoices)(B:Uniform.Before G H'.width H'.paths j X (p+3)) (u:G.ColorIndex)(W:Voice G)
variable {κ:Type} [Fintype κ] (lamps:κ→Lamp G) (collar:ℕ)

/-- Both parts use the original preselected vacuum pricing table. -/
structure FieldSent (x:ℝ):Prop where
  ordinary : Sent O K p s m j i H H' P X B u W x
  fields : ∀ (A:Mosaic.Issue G),Issue.Paid A P H H' W x → A.S.kernel=X → Festival A O p u →
    ClockD A p m s x → Cs A O s p m x u (purse Dean (hatW x) p) (bigF (seats K j i s)) →
    Issue.Receipt A (stamping (QCost O K p s j i H' P X B) s) x →
    ∀ (z:Site A.f) (Z:Positions (Primary A.c G)), ‖Z‖ ≤ hull x → ∀ part:Bool,
    FieldPort A O W p collar lamps part (tip G P.L x) ((tip G P.L x)^(Mosaic.pawn p)) z Z

variable (h:G.Simple)(hχ:LocalRatio O) (hp:Prepared K j P.L G)(hS:6 ≤ s)(hZ:m ≤ j)
    (hr:p+2 ≤ m)(hm:4 ≤ m)(hv:s ≤ j)(he:i ≤ j)(hk:P.Branches X G)(hz:P.J=j)(hU:Clear G W)
include h hχ hp hS hZ hm hv he hk hU hr hz

theorem field_card : ∀ᶠ x:ℝ in atTop,FieldSent O K p s m j i H H' P X B u W lamps collar x := by
  let M:=stamping (QCost O K p s j i H' P X B) s
  obtain ⟨c,buy,_⟩:=hp.buy P rfl s m i hv hZ he
  have funds:mortgage M P m c:=⟨⟨buy.1.pos,buy.1.high,buy.1.low⟩,buy.2⟩
  let f(x):=purse Dean (hatW x) p
  have hf:Mosaic.Run atTop id f 0:=Mosaic.Run.Ypow tendsto_id (Mosaic.Run.stanza tendsto_id) _
  have ore:∀ᶠ x:ℝ in atTop,Ore M x P:= by
    let g(x:ℝ):=Cane.value (αm x) M.C M.A M.E M.s M.sway/P.L.val
    have limit:Tendsto g atTop (𝓝 (Cane.value 0 M.C M.A M.E M.s M.sway/P.L.val)):=by
      have cont:Continuous (fun x:ℝ=>Cane.value x M.C M.A M.E M.s M.sway):=by
        unfold Cane.value Cane.candle Measuring.factor;fun_prop
      exact (cont.continuousAt.tendsto.comp (Geneva.ray (X:=id) tendsto_id)).div_const _
    exact limit.eventually (ge_mem_nhds funds.2)
  have source(part:Bool):=field_receipt O W H H' P X h hk hU hχ M u p m collar lamps part f
    (bigF (seats K j i s)) (Mosaic.pawn p) hr hm hf (by unfold Mosaic.epsW; linarith)
  filter_upwards [ore, source true, source false,
    card O K p s m j i H H' P X B u W h hχ hp hS hZ hr hm hv he hk hz hU] with x ok re im vac
  refine ⟨vac,?_⟩
  intro A paid kernel festival clock fields receipt z Z win part
  cases part
  · exact im ok A paid kernel festival clock fields receipt z Z win
  · exact re ok A paid kernel festival clock fields receipt z Z win

end YM.Integration.FVA1Physical.Round2.Curvature
