import YM.Integration.WilsonPointChildFullGauge

/-! Located older and fresh rows remain jointly admissible after the two real
filings, including all positions of each occupied subset. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildLocatedDeposit
open Function Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Winding
open FormalBulk08 Sierra Pose Stationary
open scoped Classical BigOperators
open WilsonPointChildCenteredPortfolio (bank)
open WilsonPointChildPlacedFamily (roster singleton other)
open WilsonPointChildNamedResponse (output)
open WilsonPointChildReceivedFace (mounted)
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{k h:ι→ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem located (R:Run G)(simple:G.Simple)(u:ι→G.ColorIndex)(depth:∀s,k s<h s)
    (o:Loc G 1)(digit:ι→∀i,Site (R.family.S.block i))(N j:ℕ)(live:j≤N)
    (v:∀s,Letter (R.family.labels.level (k s))):
    Wellness k (bank R u depth digit N j v):=by
  have bill:=WilsonPointChildCenteredPortfolio.lawful R u depth o simple digit N j live v
  refine ⟨fun y=>(bill y).2,fun y=>(bill y).1,?_⟩
  intro y w S same
  by_cases one:S.card=1
  · obtain ⟨s,rfl⟩:=Finset.card_eq_one.mp one
    simp only [bank,WilsonPointChildPlacedFamily.singleton,same s (Finset.mem_singleton_self s)]
  · simp only [bank,other _ one]

omit [Fintype ι] in
theorem returned (R:Run G)(simple:G.Simple)(m N:ℕ)(live:m+1<N)(T:Finset ι)
    (old fresh:Outerm G h)(before:Wellness k old)(new:Wellness k fresh)
    (z:ι→Site (ll R.family.path.levels m).L)(z':ι→Site (ll R.family.path.levels (m+1)).L):
    Wellness k (fun y=>output R.family.path.levels R.metals.O m N k T old fresh y z z'):=by
  let A:=R.family.path.levels
  refine ⟨fun y=>logHush _ _ _ _ _ _,?_,?_⟩
  · intro y
    let g:=chartIn (ll A m) y z
    let b:=old (chartIn (ll A (m+1)) g z')
    have wages:=step_L A R.metals.O (m+1) N b k live simple R.alloy.B.ratio (before.level' _)
    have cash:=WilsonPointChildReceivedFace.legal T wages (new.level' g) (logHush _ _ _ _ _ _)
    exact step_L A R.metals.O m N _ k (by omega) simple R.alloy.B.ratio cash.1
  · intro p q S same
    apply log_g
    intro J sub
    by_cases owner:J⊆T
    · simp only [mounted,if_pos owner]
      apply log_g
      intro B member
      apply before.filial
      intro s hs
      simp only [chartIn,same s (sub (member hs))]
    · simp only [mounted,if_neg owner]
      apply new.filial
      intro s hs
      simp only [chartIn,same s (sub hs)]

end YM.Integration.WilsonPointChildLocatedDeposit
end
