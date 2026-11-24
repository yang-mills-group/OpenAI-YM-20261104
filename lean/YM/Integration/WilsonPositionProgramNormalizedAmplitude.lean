import YM.Integration.WilsonPositionProgramNormalizedMaster

/-! A full normalized reported coefficient, including its surviving scalar,
is polynomially bounded on a fixed roster. This precedes the finite-to-cover
and cutoff comparisons. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramNormalizedAmplitude
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Classical BigOperators
variable {G:Gauge} {a h D k u e:ℕ} (R:Run G)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit)≤k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∃ C B:ℝ, 0<C ∧ 0<B ∧ ∃ K M:ℕ, ∀ᶠ j:ℕ in atTop, ∀X:Herit Q,
    ∀b m:ℕ,j ≤ b → b ≤ m → ∀(φ:Wilt Q)(w:Fin (a+1)→ℝ)(z:ℝ),
    Compar L.S (zz L) j m ≤ z → Bough Q φ (paceT L.S m b) z w →
    ∀t≤e,∀f:Alma ((primes G).F h),∀N,m ≤ N →
    let row:=fun n=>PowerSeries.coeff t (Reports L R.metals.O ((primes G).T h) big φ
      (normalized L R.metals.O Q X m n) m b j n k f)
    let limit:=PowerSeries.coeff t (lodgeIn L R.metals.O ((primes G).T h) big φ
      (normalized L R.metals.O Q X m) m b j k f)
    let price:=(C*z^K)*∏i,w i*((B*(zz L m)^M)*WilsonPositionProgramNormalizedMaster.fee X e i)
    ‖row N‖≤price ∧ ‖limit‖≤price := by
  intro Q L
  obtain ⟨c,wallet,ready⟩:=WilsonPositionProgramNormalizedMaster.original R simple v funded big rails l d fit cap
  refine ⟨c.x,wallet.x,zero_lt_one.trans_le c.good,zero_lt_one.trans_le wallet.good,c.d,wallet.d,?_⟩
  filter_upwards [ready] with j hear
  intro X b m late old φ w z wide fund t ht f N hired
  have paired:=((hear X b m late old φ w z wide fund t ht f).2 m N le_rfl hired)
  exact ⟨paired.main,paired.side⟩

end YM.Integration.WilsonPositionProgramNormalizedAmplitude
end
