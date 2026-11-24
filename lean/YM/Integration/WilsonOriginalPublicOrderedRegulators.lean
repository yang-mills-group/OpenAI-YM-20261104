import YM.Integration.WilsonPositionProgramNominatedOrderedReturn

/-! The independently chosen finite normalized coefficient and the original
finite-period coefficient use the same published Wilson measuring vector.  The
physical order fixes a period before exhausting its microscopic cutoffs. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicOrderedRegulators
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Fountain
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Winding WilsonCoeffUV.Layout WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNominatedRoster (selected)
open WilsonPositionProgramNominatedWinding (unitFare)
open WilsonPositionProgramNominatedPublicScalar (finite)
open WilsonPositionProgramNominatedPhysicalProfile (zoomFactor covers)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{e k u D:ℕ}
variable {I:Type} [Fintype I]



variable (arity:I→ℕ)(child:(s:I)→Fin (arity s+1)→Fin 3)(d:(s:I)→Fin (arity s+1)→ℕ)
    (fit:∀s i,levels (child s i)<d s i)
local notation "Q" => fun s=>deck (G:=G) (levels ∘ child s) (d s) (fit s)
open WilsonPositionProgramNominatedPhysicalResponse (difference)
open WilsonPositionProgramNominatedMenuInvoice (issued)

/-- Original source cutoff and period are the entries of z.  The evaluation
top and evaluation period are other indices, and change no source coordinate. -/
def reading (D:ℕ)(φ:(s:I)→Wilt (Q s))(A:Group R.family 6)
    (checked:A.station.checked f H A.horizon)(m:ℕ)(phase:Fin 3→ℂ →L[ℝ] ℝ)
    (z:ℕ×ℕ)(n p:ℕ)(s:I)(t:ℕ)(i:Alma ((primes G).F 0)):ℝ:=
  finite R (levels ∘ child s) (d s) (fit s) m n p t D
    (sceneGrow (covers R A checked) (φ s)) (selected R (child s) (d s) (fit s) A m z.1 z.2 phase) i

/-- One independent threshold for the whole finite public roster, all
retained grades and every scalar test on the actual extracted hierarchy. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(money:issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(cap:∀s,capP (Q s)≤k)
    (φ:(s:I)→Wilt (Q s))(apart:∀s i j,i≠j→Disjoint (tsupport (φ s i).ψ.val) (tsupport (φ s j).ψ.val)):
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop, 1≤zz L m → ∀A:Group R.family 6,A.station.k=m →
    ∀checked:A.station.checked f H A.horizon,∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m≤K ∧ ∀ᶠ p':ℕ in atTop,∀ n':ℕ,K≤n' →
    ∀ᶠ z in f.fuse, K≤z.1 ∧ ∀n:ℕ,K≤n → ∀s:I,∀t:Fin (e+1),∀i:Alma ((primes G).F 0),
      let read:=reading R arity child d fit D φ A checked m phase z
      ‖read n z.2 s t i-read n' p' s t i‖<ε:=by
  intro L
  have income(s:I):WilsonPositionProgramUniformWindingTable.Complete R (levels ∘ child s) (d s) (fit s)
      e unitFare 1:=WilsonPositionProgramNominatedMenuInvoice.original R simple shop money _ _ _ _ _ zero_lt_one
  have ready:=WilsonPositionProgramNominatedPhysicalResponse.original (f:=f) (H:=H) R arity child d fit
    simple _ money.1 big rails cap 1 1 zero_lt_one income φ apart
  filter_upwards [ready] with m atDate
  intro strip A date checked phase ε pos
  obtain ⟨K,mK,table⟩:=atDate strip A date checked phase (ε/2) (half_pos pos)
  refine ⟨K,mK,?_⟩
  filter_upwards [table] with p' independent
  intro n' mature
  apply (Extraction.Order.fused f _).2
  rw [Extraction.Order.late]
  filter_upwards [f.per.cofinal.eventually table] with p physical
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop (K+1)] with N high
  refine ⟨by omega,?_⟩
  intro n enough s t i read
  have h₁:=physical (f.mesh N) (f.per p) n (by omega) enough s t i
  have h₂:=independent (f.mesh N) (f.per p) n' (by omega) mature s t i
  let center:=PowerSeries.coeff t.val (lodgeIn L R.metals.O ((primes G).T 0) big
    (sceneGrow (covers R A checked) (φ s)) (normalized L R.metals.O (Q s)
      (selected R (child s) (d s) (fit s) A m (f.mesh N) (f.per p) phase) m) m m m k i)
  change ‖read n (f.per p) s t i-center‖<ε/2 at h₁
  change ‖read n' p' s t i-center‖<ε/2 at h₂
  have bound:=norm_sub_le_norm_sub_add_norm_sub (read n (f.per p) s t i) center (read n' p' s t i)
  rw [norm_sub_rev center (read n' p' s t i)] at bound
  linarith

end YM.Integration.WilsonOriginalPublicOrderedRegulators
end
