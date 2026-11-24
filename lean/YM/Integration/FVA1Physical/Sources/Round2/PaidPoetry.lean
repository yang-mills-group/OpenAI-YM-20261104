import YM.LocalLTE.Vinca.Hook
import YM.OPE.Therm.Request

/-! Thermodynamic delay requirements can be paid on the same schedule as a
finite-window source program. -/

namespace YM.PhysicalNext.Repeat.Legato.Round2

open RG RG.Supply Push.PriceCompiler Mallow

/-- Strengthen an arbitrary pre-launch price program so that any family
constructed by it also satisfies the thermodynamic flag estimates. -/
noncomputable def withPoetry {G : Gauge} {M : ℕ} (E : Elixir G M) : Elixir G M where
  invests := fun {X} {_D} {_C} {_Y} {_w} {_v} {_T} R μ ℓ e Q =>
    E.invests (X := X) R μ ℓ e Q ∧
      ∀ {b : Bar Q} (a : Wait b) (K : Levels G), Paid a K → OPE.Therm.Poetry K
  pays := by
    intro s K C Y hc μ k hk
    obtain ⟨L, hL⟩ := E.pays C Y hc μ k hk
    refine ⟨L, ?_⟩
    intro l hl D w v T R ℓ e Q
    obtain ⟨W, hQ, hw⟩ := hL l hl D R ℓ e Q
    obtain ⟨W', hW, h'⟩ := OPE.Therm.poetry_delay W
    exact ⟨W', hQ.trans hW, fun Z hZ => ⟨hw Z (hW.trans hZ), h' Z hZ⟩⟩

end YM.PhysicalNext.Repeat.Legato.Round2
