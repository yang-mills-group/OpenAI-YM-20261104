import YM.Integration.WilsonOriginalMicroscopicEntranceExchange

/-! The upper discrepancy is carried through the same physical conditional
to every earlier field, with its actual vacuum normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceEarlier
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm Marker
open WilsonOriginalMicroscopicEntranceDeposits (funded mean reading)
open WilsonThermometerSolitaryExchange (share)
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def face {T:Type*}(A:Fin 3 → T → ℂ)(s:(J).Mode)(U:T):ℂ:=∏a∈s.val,A a U

theorem salary {T:Type*}[MeasurableSpace T](A:Fin 3 → T → ℂ)(data:∀a,funded (A a))(s:(J).Mode):
    funded (face A s):=by
  choose M bounded using fun a=>(data a).2
  refine ⟨s.val.measurable_fun_prod (fun a _=>(data a).1),∏a∈s.val,M a,?_⟩
  intro U
  rw [face,norm_prod]
  exact prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>bounded a U)

theorem carry {G:Gauge}(C:Family G)(hC:C.Makes){N p K f u:ℕ}(live:K ≤ N)(stop:f ≤ K)(lower:u ≤ f)
    (F:Config G (C.side N p) → ℂ)(H:Config G (C.side K p) → ℂ)(one:funded F)(two:funded H)
    (D:Config G (C.side f p) → ℂ)
    (edge:∀U, actualTransport C (N:=N) F (stop.trans live) U - actualTransport C (N:=N) H stop U=D U)
    (W:Config G (C.side u p)):
    actualTransport C (N:=N) F (lower.trans (stop.trans live)) W-
      actualTransport C (N:=N) H (lower.trans stop) W=actualTransport C (N:=N) D lower W:=by
  obtain ⟨g,gross,bound⟩:=one
  obtain ⟨h,rent,paid⟩:=two
  have a:=actualTransport_weighted_integrable C hC (le_refl N) g.aestronglyMeasurable bound (stop.trans live)
  have b:=actualTransport_weighted_integrable C hC live h.aestronglyMeasurable paid stop
  have plus:=ActualWilsonAbsoluteTransport.sub C hC (stop.trans live) a b lower
  rw [show (fun U=>actualTransport C (N:=N) F (stop.trans live) U-actualTransport C (N:=N) H stop U)=D from funext edge,
    actualTransport_tower C hC (le_refl N),actualTransport_tower C hC live] at plus
  exact (congrFun plus W).symm

theorem original {G:Gauge}(C:Family G)(hC:C.Makes){N p K f u:ℕ}(live:K ≤ N)(stop:f ≤ K)(lower:u ≤ f)
    (A:Fin 3 → Config G (C.side N p) → ℂ)(B:Fin 3 → Config G (C.side K p) → ℂ)
    (one:∀a,funded (A a))(two:∀a,funded (B a))(s:(J).Mode)(W:Config G (C.side u p)):
    actualTransport C (N:=N) (face A s) (lower.trans (stop.trans live)) W-
      actualTransport C (N:=N) (face B s) (lower.trans stop) W=
      actualTransport C (N:=N) (fun U=>
        let x:=fun a=>mean C N (A a) f U
        let y:=fun a=>mean C N (B a) f U
        ((∑i∈Ico f N,reading C N A s.val f i U)-(∑i∈Ico f K,reading C N B s.val f i U))+
          ∑a,(x a-y a)*share x y a s) lower W:=by
  apply carry C hC live stop lower (face A s) (face B s) (salary A one s) (salary B two s)
  exact WilsonOriginalMicroscopicEntranceExchange.original C hC live stop A B one two s

end YM.Integration.WilsonOriginalMicroscopicEntranceEarlier
end
