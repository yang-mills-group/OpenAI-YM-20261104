import YM.Integration.WilsonOriginalPublicTrialInput
import YM.Integration.WilsonOriginalPublicOrderedRegulators

/-! Both finite normalized evaluations use the same true fixed-stop inverse,
including its unit. The physical order of limits is UV followed by period.
The independently sampled cutoff and side can be held fixed across that limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialRegulators
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
open WilsonOriginalPublicTrialInput (vector bill)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonPositionProgramSubmittedCoordinates (submitted)
open WilsonPositionProgramNominatedMenuInvoice (issued)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical

variable {G:Gauge}(R:Run G)(d j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
  (before:∀a,j a≤K)(trial:Indexed R d j target η M Y)
  {a e k u D:ℕ}(child:Fin (a+1)→Fin 3)(dd:Fin (a+1)→ℕ)(fit:∀s,d (child s)<dd s)
  (phase:Fin 3→ℂ →L[ℝ] ℝ)
local notation "l" => d ∘ child
local notation "Q" => deck (G:=G) l dd fit
local notation "L" => R.family.path.levels

def dose (N per:ℕ):Herit Q:=
  submitted R l dd fit (fun i=>vector R d j K target η M Y before trial N per (child i)) (phase ∘ child)

theorem income (N per e:ℕ)(s:Fin (a+1)):
    fee (dose R d j K target η M Y before trial child dd fit phase N per) e s ≤
      max 1 (bill R d j K η M e phase (child s)) :=by
  by_cases live:K<N
  · exact ((WilsonOriginalPublicTrialInput.original R d j K target η M Y before trial N per live).2.2.2
      child dd fit phase e s).2.trans (le_max_right ..)
  · apply (WilsonPositionProgramSubmittedCoordinates.paid R l dd fit _ _ e s).trans
    simp [vector, live, Labels.Frame.coeffSize]

theorem original (f:Extraction.Order)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (income₀:issued G R.kit)(big:0<D)(rails:Rails 0 k u e)(cap:capP Q≤k){δ:ℝ}(sep:0<δ):
    ∀ᶠ m:ℕ in atTop,1≤zz L m → ∀(Z:ℝ)(B:Fin (a+1)→ℝ)(ε:ℝ),0<ε →
    ∃n₀:ℕ,m≤n₀ ∧ ∀φ:Wilt Q,Compar (L).S (zz L) m m≤Z → Bough Q φ 1 Z B →
      (∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
      ∀ᶠ p':ℕ in atTop,∀n':ℕ,n₀≤n' → ∀ᶠ z:ℕ×ℕ in f.fuse,K<z.1 ∧ n₀≤z.1 ∧
      ∀n:ℕ,n₀≤n → ∀t:Fin (e+1),∀i:Alma ((primes G).F 0),
      let X:=dose R d j K target η M Y before trial child dd fit phase z.1 z.2
      let center:=PowerSeries.coeff t.val (lodgeIn L R.metals.O ((primes G).T 0) big φ
        (normalized L R.metals.O Q X m) m m m k i)
      let read(n p:ℕ):=finite R l dd fit m n p t D φ X i
      ‖read n z.2-center‖<ε ∧ ‖read n' p'-center‖<ε ∧ ‖read n z.2-read n' p'‖<ε :=by
  have ready:=WilsonPositionProgramMeteredPublicResponse.original R simple shop income₀ big rails l dd fit cap sep
  filter_upwards [ready] with m paid
  intro strip Z B ε ep
  let X:=dose R d j K target η M Y before trial child dd fit phase
  let b:=fun i=>max 1 (bill R d j K η M e phase (child i))
  obtain ⟨n₀,floor,hears⟩:=paid strip X b (fun N p _ s=>income R d j K target η M Y before trial
    child dd fit phase N p e s) Z B (ε/2) (half_pos ep)
  refine ⟨n₀,floor,?_⟩
  intro φ room shape clear
  have law:=hears φ room shape clear
  filter_upwards [law] with p' other
  intro n' grown
  apply (Extraction.Order.fused f _).2
  rw [Extraction.Order.late]
  filter_upwards [f.per.cofinal.eventually law] with p physical
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop (max K n₀+1)] with N late
  refine ⟨by omega,by omega,?_⟩
  intro n high t i X₀ center read
  have mature:m<f.mesh N:=by omega
  have first:=physical (f.mesh N) (f.per p) n mature high t i
  have second:=other (f.mesh N) (f.per p) n' mature grown t i
  change ‖read n (f.per p)-center‖<ε/2 at first
  change ‖read n' p'-center‖<ε/2 at second
  refine ⟨by linarith,by linarith,?_⟩
  have add:=norm_sub_le_norm_sub_add_norm_sub (read n (f.per p)) center (read n' p')
  rw [norm_sub_rev center (read n' p')] at add
  linarith

end YM.Integration.WilsonOriginalPublicTrialRegulators
end
