import YM.Integration.WilsonAddressedRestartedFiled
import YM.Integration.WilsonOriginalMicroscopicGuardedGrid
import YM.Integration.WilsonOriginalNullOriginGrid

/-! The upper restart at an embedded grid site is the signed difference of the
actual transported guarded stencil and the measured cutoff column. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedRestartedGrid
open Function Filter MeasureTheory Lattice RG Wilson Source Labels
open Extra.Histories Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open RG05Readout RG05Readout.Records PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonOriginalNullCorridor
open WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (d N p f : ℕ)
local notation "C₀" => R.family

def difference (n : ℕ) (live : f+n ≤ N) (o : Site ((C₀).side f p)) (w x : (C₀).label d) :
    Config G ((C₀).side f p) → ℂ :=
  let top := (C₀).S.toDepth (show f≤f+n by omega) p
  let low := (C₀).S.toDepth (show f≤N by omega) p
  carried R d live (top.embed o) w -
    dyes C₀ f N p (by omega) (((C₀).S.a f:ℂ)^d •
      (C₀).O N p (((C₀).factory d N p).terminal x) (low.embed o))

theorem grid (n : ℕ) (live : f+n ≤ N) (age : (C₀).ref d ≤ f)
    (o : Site ((C₀).side f p)) (w x : (C₀).label d) :
    difference R d N p f n live o w x =
      (track R d N p (f+n) (numerator R d N p (f+n) 0 w) f -
        calValues (C:=C₀) d N p f x) ∘ Lattice.translate o := by
  have move := WilsonOriginalMicroscopicGuardedGrid.carried_on R d N p f n live o w
  have orig := WilsonOriginalNullOriginGrid.public_grid R d N p (show f ≤ N by omega) age o x
  have cut := segment R d N p (numerator R d N p (f+n) 0 w) n (le_refl (f+n))
  rw [at_top] at cut
  dsimp only [difference]
  rw [move,orig,cut]
  rfl

theorem original (simple : G.Simple) : ∀ᶠ j : ℕ in atTop,
    ∀ N p f n (before : j ≤ f+n) (high : f+n ≤ N) (target : ℕ) (η : ℝ)
      (M : (C₀).label d ≃ₗ[ℂ] (C₀).label d) (x : (C₀).label d),
    let e := page (C:=C₀) d p j (((C₀).factory d N p).entries j x)
    let w := M.symm e
    let B := hike C₀ (f+n) f rate*((1+4*stock C₀ (f+n))*((C₀).labels.level d).coeffSize w)
    Arrived R d j (f+n) N p target before high η M e →
    j ≤ f → ∀ o : Site ((C₀).side f p), ∃ z : store C₀ d p f,
      WilsonAddressedRestartedFiled.Filed R d N p f o
        (track R d N p (f+n) (numerator R d N p (f+n) 0 w) f-calValues (C:=C₀) d N p f x) B z ∧
      z.density o ((C₀).localSection d) ((C₀).path.rep N p f) = difference R d N p f n high o w x := by
  filter_upwards [WilsonAddressedRestartedFiled.original R d simple,eventually_ge_atTop ((C₀).ref d)] with j sold age
  intro N p f n before high target η M x e w B arrived jf o
  obtain ⟨z,file⟩ := sold N p (f+n) before high target η M x arrived f jf (by omega) o
  exact ⟨z,file,file.field.trans (grid R d N p f n high (age.trans jf) o w x).symm⟩

end YM.Integration.WilsonAddressedRestartedGrid
end
