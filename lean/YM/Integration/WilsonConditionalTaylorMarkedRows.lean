import YM.Integration.WilsonConditionalTaylorMarkedInlet
import YM.Integration.WilsonConditionalTaylorBulkShape

/-! Finite signed normalized integral of a varying whole occupied row under
the same changing Wilson/Haar partition function as the unmarked course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedRows
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open WilsonConditionalTaylorBulkRows WilsonConditionalTaylorMarkedInlet
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {j t l : ℕ} (P : Flight j t) (L : Lodge P.patch) (ρ : ChartRatio G)
    (h : P.patch.Branches K G) (n : Side) (k : (primary P.patch K n).Choices) (U Z : Pap (wire G (n*P.L)))

def dates := dipper ((rayshot P L h).acts n) (swim ((rayshot P L h).acts n)
  (rancho (inlet P L ρ h n k U))) (rancho (bank P L h n Z))

private theorem mapZero {I J : Type*} {r : ℕ} (A : I → J → ℝ) (T : Tile I r) (z : T=0) :
    Lava.pearl A T=0 := (congrArg (fun v=>Lava.pearl A v) z).trans (Lava.pearl_zero A r)

theorem income (room : 4 ≤ t) (shape : Young (rancho Z) l) : Young (rancho (bank P L h n Z)) l :=by
  obtain ⟨s,C,hs,hC,hk⟩:=aone P (K:=K) G room
  intro e r hv
  apply shape e r
  intro hZ
  apply hv
  rw [rows P L h n Z e r hs hC hk,hZ,jetty_zero]
  exact mapZero _ _ (mapZero _ _ (mapZero _ _ rfl))

theorem read (hr : LocalRatio ρ) (room : 4 ≤ t) (head : coeff 0 U=crunch (kernelP G K.penalty P.wing _))
    (old : WilsonConditionalTaylorBulkShape.Ranks U) (shape : Young (rancho Z) l) (u : ℕ) (hu : l≤u) (e r : ℕ) :
    rancho (Reef.tossed P ρ h L n k U Z) e r = ∑ i∈Finset.range (u+3*e+1),
      jetty (coastRight _ _ _) (dates P L ρ h n k U Z i e r) :=by
  let F:=ferry P h L n
  let E:=saddleP G (primary P.patch K n) L
  let p:=flush (Reef.floor K P L n) k ρ U
  let J:=Reef.seat (Reef.floor K P L n) Z
  let A:=rancho (cobalt F p)
  let B:=rancho (inlet P L ρ h n k U)
  let T:=rancho (bank P L h n Z)
  let M:=rancho (lever F J)
  let Q:=(rayshot P L h).acts n
  let q:=aqua F.saddle (I:=wire G n)
  have hB:=WilsonConditionalTaylorBulkShape.paid P L ρ h n k U hr room old
  have fin : Fiery A:=fun i d nonzero=>hB i d fun hz=>nonzero ((Bank.quake (cobalt F p) E i d).mpr hz)
  have fee:=income P L h n Z room shape
  have mark : Young M l:=fun i d nonzero=>fee i d fun hz=>nonzero ((Bank.quake (lever F J) E i d).mpr hz)
  have solvent:=Reef.consolidate P ρ h L n hr k U head room
  have wireEq:∀ i d,A i d=jetty E (B i d):=fun i d=>infer_joust E _ i d
  have eqQ:∀ u v,Q (E u) (E v)=q u v:=ray_forms P L h n
  have markedEq:∀ i d,M i d=jetty E (T i d):=fun i d=>infer_joust E _ i d
  have waves:∀ m e r,swim q A m e r=jetty E (swim Q B m e r):=fun m e r=>(dye_swim E q Q eqQ B A wireEq m e r).symm
  change rancho (flag F p J) e r=_
  rw [extraction_mark F p J solvent fin mark e r (u+3*e) (by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←show jetty E (dates P L ρ h n k U Z i e r)=_ from dye_dip E q Q eqQ (swim Q B) T (swim q A) M waves markedEq _ _ _]
  rfl

theorem output (hr : LocalRatio ρ) (room : 4 ≤ t) (head : coeff 0 U=crunch (kernelP G K.penalty P.wing _))
    (old : WilsonConditionalTaylorBulkShape.Ranks U) (shape : Young (rancho Z) l) : Young (rancho (Reef.tossed P ρ h L n k U Z)) l :=by
  intro e r live
  by_contra high
  apply live
  rw [read P L ρ h n k U Z hr room head old shape l le_rfl e r]
  apply Finset.sum_eq_zero;intro i _
  have z : dates P L ρ h n k U Z i e r=0:=by
    by_contra seen
    exact high ((youth_egg _ (income P L h n Z room shape) (WilsonConditionalTaylorBulkShape.paid P L ρ h n k U hr room old) i e r seen).1)
  rw [z,jetty_zero]

end YM.Integration.WilsonConditionalTaylorMarkedRows
end

