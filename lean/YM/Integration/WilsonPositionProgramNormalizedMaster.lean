import YM.Integration.WilsonMarkedIndependentNormalizedReporter

/-! A common explicit fee for a normalized master before either UV cutoff and for every soft stop. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramNormalizedMaster
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}

open WilsonMarkedIndependentNormalizedElection (deck normalized)


def fee {Q : Fin (a+1) → SealR G} (X : Herit Q) (e : ℕ) (i : Fin (a+1)) : ℝ :=
  ∑ j : Alma (Q i).F, ∑ r : Fin (e+1), ‖PowerSeries.coeff r.val ((X i) j)‖

theorem shipped {Q : Fin (a+1) → SealR G} (X : Herit Q) (e : ℕ) (S : Schedule) (m : ℕ) :
    Shipment S m Q (fee X e) e (fun _ => X) := by
  let P := fee X e
  have hp i : 0 ≤ P i := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine fun _ _ _ _ _ _ => ⟨hp, ?_⟩
  intro i j hj l
  let v : Fin (e+1) := ⟨j, by omega⟩
  apply twain.one _ _ (trail_pos ..).le
  exact (Finset.single_le_sum (f:=fun r:Fin (e+1)=> ‖PowerSeries.coeff r.val ((X i) l)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum (f:=fun t=> ∑ r:Fin (e+1), ‖PowerSeries.coeff r.val ((X i) t)‖)
      (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ l))

theorem original (R : Run G) (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (admit : ∀ i, l i < d i)
    (cap : capP (deck (G:=G) l d admit) ≤ k) :
    let Q := deck (G:=G) l d admit
    let L := R.family.path.levels
    ∃ c wallet : Credit, ∀ᶠ j : ℕ in atTop, ∀ X : Herit Q,
      WilsonMarkedIndependentNormalizedReporter.Reading Q L R.metals.O (zz L) ((primes G).T h)
        p k e c wallet j X (fee X e) := by
  intro Q L
  obtain ⟨c,report⟩:=reportUV (hol G) Q ((primes G).T h) p rails cap Credit.leanC Credit.leanC
    Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  obtain ⟨wallet,lens⟩:=steering (hol G) Q e Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  refine ⟨c,wallet,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap]
    with j filed
  obtain ⟨W,Y,level,cash,clock,date,agree,dorm,spring,frames,ready⟩ := filed
  intro X
  have receives : WilsonMarkedIndependentNormalizedReporter.Reading Q Y.L.V.draws Y.L.V.paid
      Y.L.V.y ((primes G).T h) p k e c wallet Y.L.V.anchor X (fee X e) := by
    intro b m jb bm φ B z leg shape i he f
    have stock := lens Y.L.V frames m (jb.trans bm) (fee X e) (fun _=>X)
      (shipped X e Y.L.V.draws.S m)
    exact report Y W agree ready spring dorm m b Y.L.V.anchor φ
      (normalized Y.L.V.draws Y.L.V.paid Q X m) (fun s=>Y.L.V.cash wallet m*(fee X e s)) B z
      le_rfl jb bm leg shape stock i he f
  rwa [level,cash,clock,date] at receives

end YM.Integration.WilsonPositionProgramNormalizedMaster
end
