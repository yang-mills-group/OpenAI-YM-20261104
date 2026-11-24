import YM.Integration.WilsonPositionProgramMasterBirth

/-! At each real center and each genuine child the submitted root of the
normalized master is translated on the finite torus. Its true moving test
and every reannounced coupling coefficient are read before the subsequent
block or any scalar projection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramLocatedMaster
open Finset Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext.Repeat.Legato Labels Source
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonCoeffUV.Soil
open scoped Classical BigOperators Topology
variable {G : Gauge} {h D : ℕ} (R : Run G)
local notation "F" => R.family.labels.level h
local notation "T" => R.family.localSection h
local notation "L" => R.family.path.levels

theorem root (fit : h < D) (m N : ℕ) (n : Side) (t y : ℝ) (x : Cover) (c : CellR)
    (φ : Rarity D) (X : Verse F) :
    let Q := BayV (primes G) h D fit
    let v := PermuteLens L R.metals.O Q N m X
    let w := steep L R.metals.O T fit N m (N-m) v
    let Y := WilsonCoeffUV.Wheel.Mark.centralL L R.metals.O N m N Q v
    let b := wheelC t y x φ.ψ c
    let F₀ := loom (spear (jog (wrap n x) : Woods G n ≃ Woods G n))
    let H := WilsonPositionProgramMasterBirth.rank R (d:=h)
    On h Y → PowerSeries.X^H * flash ((locale c (shoe Y φ t y x)).1 n) =
      F₀ (∑ s, PowerSeries.X^(H-valence F s) * Blue.soil (w s) *
        (jewelBloom fit s b • jet (Plies T (sheet F s) n))) := by
  intro Q v w Y b F₀ H on
  have hs := (On_auth on).span n
  change PowerSeries.X^H * flash (fun i k => revolve (wrap n x) ((jot b (Y.1 n)) i k)) = _
  rw [translate_value n (wrap n x) _ (jot_length b hs)]
  have born := WilsonPositionProgramMasterBirth.original R fit N m n X b
  change PowerSeries.X^H * flash (jot b (Y.1 n)) = _ at born
  rw [←born,map_mul,map_pow]
  simp [F₀,loom]

end YM.Integration.WilsonPositionProgramLocatedMaster
end
