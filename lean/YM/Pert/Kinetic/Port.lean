import YM.Pert.Kinetic.Cap
import YM.Pert.Supply.End
/-! Actual-law kinetic rigidity for the perturbative comparison, through the same Wilson coupling and shared levels as budgetEndpoint. Sign convention: `error_of_cost` is only replacement of a beta in an exactly equal `RG.Rep.eval`. This does not compare correlation coefficients in different frames or construct a PT diagram counterterm. -/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG MeasureTheory Asymptotics Bid Source
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(hG:G.Simple)
local notation "A" => C.path.levels
local notation "P" => (A).clock

/-- All varying cutoffs, on this exact history simultaneously with old kernel clocks. Any equal lawful rerendering of the density with common indicated weak size budgets changes the kinetic by at most the given inverse powers, uniformly even without a kinetic-band assumption on its own separate beta. -/
structure Conversion (C₁ : Family G) : Prop where
    fits (Nq : ℕ) : ∀ᶠ m in atTop, ∀ N (h : m ≤ N) p, ∀ (R : Rep G (C₁.side m p)), let H:= C₁.path.levels.clock.hatBeta m;
       R.eval=(C₁.path.rep N p m).eval → ∀ (σ L Λ δ w : ℝ), R.Lawful σ L Λ δ w → Quotes R.p σ L Λ δ (2*H) → |R.beta-C₁.path.β N p m| ≤ ((2*H)^Nq)⁻¹
include hG
lemma converted (h : YM.MergeProof.Ribbons.Plenty C)(ht:C.Makes) : Conversion C := by
   constructor; intro q
   filter_upwards [paid_tail C hG h,stay C hG 9 (2*Real.pi^2*(2*(Fintype.card PlaqAxes:ℝ))), stay C hG (9+q) (4*Real.pi^2*coefK)] with m hm h1 h2 N he p R
   dsimp only; intro hir σ L Λ δ w hr hR
   let s := 2*(P).hatBeta m; let old := C.path.rep N p m
   let n := C.side m p
   have hg := ht.wilson.represents N p m he
   have hM := hm N p
   let d:ℝ:=Fintype.card PlaqAxes
   have hs : Real.pi^2*Full.mesh n*(2*d*s^9) ≤ (1/2:ℝ):= by have hs:|2*Real.pi^2*(2*d)|=2*Real.pi^2*(2*d):=abs_of_nonneg (by unfold d; positivity); apply (le_div_iff₀ zero_lt_two).2; change _ ≤ _ ; linarith only [show s^9*(2*Real.pi^2*(2*d))*Full.mesh n ≤ 1 from hs ▸ h1 p]
   have hh:= small_beta hG hir.symm hr hg.good (hg.vac.symm ▸ hM.1) hR (show 4≤(C.side m p).val from by have hb:=(A).fits.sizeT m p; change _ ≤ (C.side m p).val at hb; omega) (hM.2 hg) hs
   rw [abs_sub_comm]; refine hh.trans ?_; rw [←one_div]; apply (le_div_iff₀ (by have := (A).fits.delayed m; positivity)).2 -- lemma name
   have h2p := h2 p
   rw [abs_of_pos (by have h:=coefK_pos; positivity : 0 < (4:ℝ) * Real.pi ^ 2 * coefK)] at h2p
   refine Eq.trans_le ?_ h2p
   change 4 * Real.pi^2 * coefK * s^9 * Full.mesh n * s^q = (s^(9+q))*(4*Real.pi^2*coefK)*Full.mesh n
   rw [pow_add];ring
end YM.Pert.Kinetic
