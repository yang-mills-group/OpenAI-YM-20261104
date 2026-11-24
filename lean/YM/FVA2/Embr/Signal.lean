import YM.FVA2.Embr.Visible
/-!
 # Fk.Steady readout on the true tagged finite inversion epoch

 `posts` strengthens `Hearth.prophecy` to using entered `Planet`
 with STEADY, AND actual approved transition weights at optional
 mixture (here with the likelihood from true `StepData`, on constrained
 probe fields, not pretending same cost of ordinary torus).
 The theorems keep exact branch count and thermostat budget. No
 analytic estimator on cover hierarchy from these results. Cost of
 obtaining these planets *after* fixing their Geometry,y,N, etc.
 In particular not claiming any uniformity in size of regulator!
 Powers reported after contraction use the full conditional partition
 function (incl reconstructed scalar determinant) as usual.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Hearth.Clan RGComparison.Core16 Lumen Fk Forge
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side} {L:Fabric G n}{T:Cloth L}{w:L.Accounts→ℝ→ℝ}
variable {y:Flats G (Bottom L)}{s:G.ColorIndex}{Ω:Lumen.Shelf G Unit (Warm T)} {j:Warm T→Site n}
local notation "P"=> home T w y s Ω j
open Arrival
variable (F:Habitat T w y s Ω)(Y:XSpace.Initialize G)(l:List (Folio G)){J:ChartRatio G}(hj:LocalRatio J)
local notation "A"=> markValue Y l n
local notation "V"=> scroll (Folio.scenario Y n l) T y
local notation "H_" => lens T y s ( Hearth.rad T ( Folio.scenario Y n l ))
include F hj
lemma reckons : Aspiration (Fk.baron P V (Folio.asset l)) ( Fk.read P J (tease T s) H_ (Folio.asset l)):= by
 obtain ⟨b,hB⟩:= seen F (Folio.scenario Y n l) (Folio.matured Y n l L.even)
 exact Fk.exterior (F.resolves j) hj hB (charges_ok T y s Y l) (canopy _ _ _ _ (challenged Y l L.even))

variable (z:L.Accounts→ PowerSeries ℝ)(hz:∀ i,0<term (z i) 0)(N:ℕ) (he:∀ i,Through N (amount (w i)) (z i))(hp:∀ i,ContDiffAt ℝ ω (w i) 0)
local notation "χ" => (Facade.drive T (z∘some) (Facade.headquarters z) )
set_option quotPrecheck false
local notation "G!" => Stack.read y (Facade.drive T (z∘some) (Facade.headquarters z) A J (collared T z hj hz)).2
include he hp hz
lemma posts (k:ℕ)(hk:Folio.asset l + k ≤ N) : Fk.read P J (tease T s) H_ (Folio.asset l) k= PowerSeries.coeff k G! := by rw [Fk.read,←harvestVal j F]; exact Hearth.prophecy Y T l z hz hj s y w N hp he k hk
lemma income : Through N (PowerSeries.mk (Fk.birth P J)) (PowerSeries.C (overheadC T z hz y J) * Stack.read y (χ A J (collared T z hj hz)).1.W):= by
 have hB : Fk.birth P J= Fk.birth (Hearth.localClimate T y s w) J:= (RightHarvest j F J Fk.vacant (fun _:Empty→G.Color=> (1:ℝ))).symm; rw [hB,Hearth.launch_vacant]; exact Facade.sales T z hj hz w y hp N he A
lemma report_general (O:Wilson.Config G n→ℝ)(hO:PreTest O)(k d:ℕ)(hk:d+k≤N) : Fk.read P J (tease T s) (lens T y s ( Hearth.rad T O)) d k= PowerSeries.coeff (d+k) (Stack.read y (Facade.drive T (z∘some) (Facade.headquarters z) (imprintRoot O) J (collared T z hj hz)).2):= by rw [Fk.read,← harvestVal j F]; exact Hearth.predicted T y s w hj z hz N hp he O hO d k hk
omit F hj
variable (T w)
/-- Choose AT WILL any marked-word demand, any required accuracy through one shelf
 & authorization which includes truth of likelihood branch etc., at fixed physical
 y. `Hearth.prophecy` & partners (e.g. `Recall/`) applicable to this same
 conditional. Condition `k+asset ≤ N` separate from what gets output.
 Adjust $w$ to polynomial clock when rendering through $N$ and entry witnesses
 `hp` via for example `Hearth.Clock`; no assumption about convergence of the
 formal expansions. Estimates in Aspiration are on this auxiliary generator at FIXED
 finite data. PP.
 -/
theorem sponsors (y: Flats G (Bottom L)) (s:G.ColorIndex): ∃ Ω, Habitat T w y s Ω ∧ ∀ (j:Warm T→Site n)(l : List (Folio G))(J:ChartRatio G)(hj:LocalRatio J), let P0:= home T w y s Ω j; let V0:= scroll (Folio.scenario Y n l) T y; let Z(k):= Fk.read P0 J (tease T s) (lens T y s ( Hearth.rad T (Folio.scenario Y n l) )) (Folio.asset l) k; Aspiration (Fk.baron P0 V0 (Folio.asset l)) Z ∧ ∀ k:ℕ,Folio.asset l+k≤N → Z k=PowerSeries.coeff k (Stack.read y (Facade.drive T (z∘some) (Facade.headquarters z) (markValue Y l n) J (collared T z hj hz)).2):= by
  obtain ⟨Ω,hΩ⟩:= enroll T w y s hz he hp; exact ⟨ Ω,hΩ,fun j l J hj => ⟨ reckons hΩ Y l hj, Embr.posts hΩ Y l hj z hz N he hp ⟩ ⟩
end YM.FVA2.Embr
