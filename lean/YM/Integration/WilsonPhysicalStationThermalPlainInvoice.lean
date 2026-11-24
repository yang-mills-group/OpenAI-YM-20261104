import YM.Integration.WilsonPhysicalStationThermalPlain

/-! On the original quiet, the unamplified higher raw rows share one
calendar threshold across the whole prescribed panel aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalPlainInvoice
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Function Filter Set Lattice Wilson RG Labels Pressure Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open Source Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal Next.Rank.Ribbon MergeProof.Accent Extra.Histories PhysicalNext.Repeat.Legato.Bandage
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalThermalWickStretched (rates)
open WilsonReporterWeightedRankPrice (heats)
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {W:Bid.Worth} {u₀ ψ φ δ:ℕ→ℝ} {r:ℕ→ℕ}
    {door:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (B:Binding C) (H:C.Makes) (h:G.Simple)
    (source:Scrim C W u₀ ψ φ δ (fly C.path.levels) r door)
    (O:HaarBudget G) (J:ChartRatio G) {u D dSmall:ℕ} {d:Fin 2→ℕ}
    (g:(i:Fin 2)→C.label (d i)) {K:Set (Points 2)}
local notation "AX"=>C.path.levels

include h source
theorem paid (θ:ℕ)(e upper z:ℝ)(amounts:∀i≤D,generator G i≤z)(two:2≤u)
    (grade:∀i,d i≤D)(compact:IsCompact K)(clear:K⊆conf 2)(A:ℝ)
    (range:∀y∈K,Poly.price (fun _=>1) (Read.maxProfile C y (jointX g))≤A):
    ∀ᶠ k:ℕ in atTop,∀pan:Tapes.Panel D,pan.θ=θ→pan.currency=e→pan.arc≤upper→
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K) g pan (fun _=>0) k A z:=by
  classical
  let P:Type:={pan:Tapes.Panel D // pan.θ=θ ∧ pan.currency=e ∧ pan.arc≤upper}
  by_cases pop:Nonempty P
  · let ok (k:ℕ)(v:P):Prop:=WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K) g v.val (fun _=>0) k A z
    let witness (k:ℕ):P:=if bad:∃v:P,¬ok k v then bad.choose else Classical.choice pop
    have periods:=WilsonPhysicalStationThermalPlain.stage B H h source O J g (fun k=>(witness k).val) θ e upper z
        (fun k=>(witness k).property.1) (fun k=>(witness k).property.2.1) (fun k=>(witness k).property.2.2)
        amounts two grade compact clear A range
    filter_upwards [periods] with k all
    intro pan cash cost budget
    by_contra missing
    have bad:∃v:P,¬ok k v:=⟨⟨pan,cash,cost,budget⟩,missing⟩
    have receipt:ok k (witness k):=all
    have sel:witness k=bad.choose:=dif_pos bad
    exact bad.choose_spec (sel ▸ receipt)
  · exact Filter.Eventually.of_forall fun _ pan e₁ e₂ e₃=>(pop ⟨⟨pan,e₁,e₂,e₃⟩⟩).elim

end YM.Integration.WilsonPhysicalStationThermalPlainInvoice
end
