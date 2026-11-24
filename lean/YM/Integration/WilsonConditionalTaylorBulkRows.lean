import YM.FormalBulk08.Bank.Tee

/-! The actual connected finite Wilson recurrence for an arbitrary prescribed
predecessor at the same vertices. The predecessor need not equal the periodized
infinite action. The quadratic head, field ranks and parity are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkRows
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (ρ : ChartRatio G)
    (h : P.patch.Branches K G) (n : Side) (k : (primary P.patch K n).Choices) (U : Pap (wire G (n*P.L)))

def inlet := joust (saddleP G (primary P.patch K n) L)
  (cobalt (ferry P h L n) (flush (Reef.floor K P L n) k ρ U))

def connected (e r : ℕ) := ∑ b∈Finset.range (3*e+1), jetty (coastRight _ _ _)
  (swim ((rayshot P L h).acts n) (rancho (inlet P L ρ h n k U)) b e r)

theorem read (hr : LocalRatio ρ) (room : 4 ≤ t) (head : coeff 0 U=crunch (kernelP G K.penalty P.wing _))
    (shape : Fiery (rancho (inlet P L ρ h n k U))) (e r : ℕ) :
    rancho (Reef.landed P ρ h L n k U) (e+1) r=connected P L ρ h n k U (e+1) r := by
  let B:=primary P.patch K n
  let H:=ferry P h L n
  let E:=saddleP G B L
  let p:=flush (Reef.floor K P L n) k ρ U
  let A:=rancho (cobalt H p)
  let V:=rancho (inlet P L ρ h n k U)
  have fiery : Fiery A:=fun i d nonzero=>shape i d fun hz=>nonzero ((Bank.quake (cobalt H p) E i d).mpr hz)
  have honest:=Reef.consolidate P ρ h L n hr k U head room
  change marble _ (coeff _ (out H p))=_
  rw [extraction H p honest A rfl fiery]
  unfold connected
  apply Finset.sum_congr rfl
  intro b hi
  have wireEq:∀ i d, A i d=jetty E (V i d):=fun i d=>infer_joust E _ i d
  rw [←dye_swim E (aqua H.saddle) ((rayshot P L h).acts n) (ray_forms P L h n) V A wireEq]
  rfl

end YM.Integration.WilsonConditionalTaylorBulkRows
end

