import YM.Integration.WilsonConditionalTaylorThermalPolynomial
import YangMills.WilsonProof.NativeSupport.ThermalJets

/-! Every finite slot of a true local section has its own physical face,
color, position and coefficient on the incoming Descent. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalStencil
open Function Filter Lattice RG Tree Wilson Labels Source Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested
open ThermalShortcuts.ThermalJets
open scoped Topology Classical BigOperators
variable {G : Gauge} {n c D : ℕ} {a b : Side} {F : Frame G D}

structure Stencil (T : SectionData F) (i : F.Index) where
  arity : ℕ
  slot : Fin arity → Slot
  polynomial : Bid.Pose G arity
  evaluates : T.evaluate (Pi.single i 1) = Bid.lumin polynomial ∘ Bid.mapped slot
  lowest : Bid.lows polynomial (F.grades i).2

def recorded {T : SectionData F} (bank : Bid.pop T) (i : F.Index) : Stencil T i := by
  classical
  let data := Classical.choose_spec (bank i)
  let row := Classical.choose_spec data
  let p := Classical.choose_spec row.2
  exact ⟨_,_,_,p.1,p.2⟩

variable {T : SectionData F} {i : F.Index} (S : Stencil T i) (d : Descent a b) (o : Site a)

def coordinates (y : Coordinates G d) (k : Fin S.arity × G.ColorIndex) : ℂ :=
  ((leg G d (Work.F03.slotFace (S.slot k.1) o) k.2) y : ℝ)

def head (y : Coordinates G d) :=
  WilsonConditionalTaylorThermalPolynomial.entered S.polynomial (F.grades i).2 (coordinates S d o y)

theorem original (x : Coordinates G d) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹ ^ (F.grades i).2) *
      T.places (Pi.single i 1) o (d.fine 1 (d.tablePath (t • x)))) (𝓝[≠] 0) (𝓝 (head S d o x)) := by
  let v (t : ℝ) (j : Fin S.arity × G.ColorIndex) : ℂ :=
    ((S.slot j.1).atSite (represent (t • topDir d x)) o) j.2
  have hs (j : Fin S.arity × G.ColorIndex) : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * v t j) (𝓝[≠] 0)
      (𝓝 (coordinates S d o x j)) := by
    let read : G.Color → ℂ := fun y => (y j.2 : ℝ)
    have hc : Continuous read := by dsimp [read]; fun_prop
    have raw := (hc.tendsto _).comp (Work.F03.slot_limit (S.slot j.1) o (topDir d x))
    refine raw.congr' (Filter.Eventually.of_forall fun t => ?_)
    change (((t⁻¹ • (S.slot j.1).atSite (represent (t • topDir d x)) o) j.2 : ℝ) : ℂ) = _
    rw [PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
  have h := WilsonConditionalTaylorThermalPolynomial.original S.polynomial (F.grades i).2 S.lowest
    v (coordinates S d o x) hs
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
  change _ = _ * T.evaluate _ (expandAt o (d.fine 1 (d.tablePath (t • x))))
  rw [S.evaluates,path_top,map_smul]
  simp only [Function.comp_apply,Bid.lumin,MvPolynomial.aeval_eq_eval₂Hom]
  rfl

end YM.Integration.WilsonConditionalTaylorThermalStencil
