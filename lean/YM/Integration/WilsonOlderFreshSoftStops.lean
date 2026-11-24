import YM.Integration.WilsonOlderFreshHybridOneLaw
import YM.Integration.WilsonOlderFreshTerminalProgramme

/-! Hear the nonbare K-planted programme on its earlier weak date, with every
rank entering the original normalized transfer and one charge for all its first joins. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOlderFreshSoftStops
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Topology BigOperators Classical
variable {G : Gauge} {a h D k u e : ℕ}

open WilsonOriginalPublicTwoTopJoined (Hearing)
open WilsonMarkedIndependentNormalizedElection (deck normalized)


open WilsonOlderFreshHybridClock (flat)
open WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Fountain

def scalarOnly (P:Era G ℝ):Era G ℝ:=P-axeR P

theorem filed (P:Era G ℝ)(j:ℕ):
    (scalarOnly P).2 j 0=P.2 j 0 ∧ ∀r>0,(scalarOnly P).2 j r=0:=by
  constructor
  · change P.2 j 0-lop P.2 j 0=_
    simp [lop]
  · intro r hr
    change P.2 j r-lop P.2 j r=0
    simp [lop,Nat.ne_of_gt hr]

theorem received (G:Gauge)(k e u:ℕ)(E W:Credit):
    ∃U V:Credit,∀(S:Realm G (e+1) E),Dormitory S k u W →
      ∀(v w c N:ℕ)(Z A:ℝ),S.anchor ≤ v → v ≤ w → w ≤ c → c ≤ N →
      PadRank S v w Z → 0 ≤ A →
      ∀(P:Era G ℝ),Auth k P → Saturation e 1 u P.2 1 A →
      let H:=cruises S.draws S.paid N k c w P
      let H₀:=scalarOnly H
      let full:=cruises S.draws S.paid N k c v P
      let deposit:=cruises S.draws S.paid N k w v H₀
      let fee:=S.cash U w*S.tempC w c*A
      Saturation e 1 u H.2 1 fee ∧
        Saturation e 0 u (full-deposit).2 1 (V.buy Z*fee):=by
  obtain ⟨U,shrink⟩:=beamGo G k e u E W
  obtain ⟨V,charge⟩:=bulkCert G k e u E W
  refine ⟨U,V,?_⟩
  intro S dorm v w c N Z A hv vw wc cn room an P authentic gross H H₀ full deposit fee
  have hi:=hv.trans vw
  have wN:=wc.trans cn
  have wh:Auth k H:=cruising S.draws S.hG S.green wc cn authentic
  have wn:0 ≤ fee:=mul_nonneg (mul_nonneg (zero_le_one.trans (U.purchase (S.depth _ hi)))
    (trail_pos ..).le) an
  have payable:Saturation e 1 u H.2 1 fee:=fun i he r hr=>
    shrink i he r S dorm w c (fun _=>1) (oldGuard hi wc) N P A authentic cn an gross hr
  refine ⟨payable,?_⟩
  have sale:Saturation e 0 u (axeR H).2 1 fee:=by
    intro i ie r _
    cases r with
    | zero=> simp only [axeR,lop,↓reduceIte]; exact Fruit.zero.more wn
    | succ r=>simpa only [axeR,lop,if_neg (Nat.succ_ne_zero r)] using payable i ie (r+1) (by omega)
  have keep:Auth k H₀:=wh.sub wh.axe
  have signed:H-H₀=axeR H:=by dsimp [H₀,scalarOnly];abel
  have transport:=cruisePlus S.draws vw S.hG S.green wN wh keep
  rw [signed] at transport
  have difference:full-deposit=cruises S.draws S.paid N k w v (axeR H):=by
    rw [transport];change cruises _ _ N k c v P-_=_
    rw [cruisesMore S.draws S.paid P vw wc]
  rw [difference]
  intro i ie r _
  exact charge i ie r S dorm v w (fun _=>1) N Z (oldGuard hv vw) room wN _ fee wh.axe wn sale

end YM.Integration.WilsonOlderFreshSoftStops
