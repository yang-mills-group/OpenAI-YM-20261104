import YM.Integration.WilsonSeparatedPrefixGradedOpticalClear
import YM.Next.RANK.LineBox
import YM.Vac.Shelter

/-! The original flat field and its actual finite determining fields satisfy the terminal hypotheses on the preselected course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClock
open Function Filter Finset Lattice Wilson RG Source Labels Next.Rank.Spindle PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
theorem original (simple:G.Simple):
    ∀ᶠ j:ℕ in atTop,∀(N p b:ℕ)(o:Site (R.family.side j p))(x:Space G o b),
    ‖x‖ ≤ (H j^6)⁻¹ → flags (R.family.path.rep N p j).p.threshold
      (net (R.family.path.rep N p j).p o b x)=∅:=by
  obtain ⟨S⟩:=charts G
  have rise:Tendsto (fun i:ℕ=>(H i)^6) atTop atTop:=
    (tendsto_pow_atTop (α:=ℝ) (n:=6) (by norm_num)).comp (RG01.Physical.hats simple (A))
  have shrink:Tendsto (fun i:ℕ=>((H i)^6)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp rise
  filter_upwards [shrink.eventually (ge_mem_nhds (pane_pos S))] with j cap N p b o x nx
  exact voids (occupied _ x S (nx.trans cap)) le_rfl

end YM.Integration.WilsonSeparatedPrefixCanonicalClock
end
