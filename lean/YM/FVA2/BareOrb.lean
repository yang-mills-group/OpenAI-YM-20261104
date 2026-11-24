import YM.FVA2.TreeLaplace
import YM.FVA2.OrbGerm

/-!
# Tree-invariance / Orb bridge of the XSpace bare coefficients
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2
open MeasureTheory Function Set Filter Lattice XSpace PertExtension
open scoped Topology BigOperators Classical ENNReal ContDiff
variable {G:Gauge}{R:Period}(T:R.Tree){O:Wilson.Config G R.side→ℝ}

namespace BareOrb
abbrev sample (O:Wilson.Config G R.side→ℝ) := O ∘ R.restore ∘ T.drape
def stencil (O:Wilson.Config G R.side→ℝ) := TreeFormal.enter T (O ∘ T.links)
lemma sampling (O:Wilson.Config G R.side→ℝ) : O ∘ T.links=sample T O ∘ Chart.expLinks G T.Free:=rfl

lemma identity (t:ℝ) (hx: ∀ u : Site R.side → G.El, (∀ x,u (-x)=u x) → ∀ x, O (gauge u x)=O x)(h:Continuous O):
   (∫ u,TreeFormal.billrow T (sample T O) t u ∂T.measure G) = Orb.numerator (Orb.restrictedO O) t:=by
  let V:=O * Orb.preDensity (n:=R.side) t
  have hF:Continuous V:= by
     apply h.mul; unfold Orb.preDensity; fun_prop
  have hv:∀ u : Site R.side → G.El, (∀ x,u (-x)=u x) → ∀ x, V (gauge u x)=V x:=by
     intro k hk x; change O _ * Real.exp _=O x * Real.exp _; rw [hx k hk,Wilson.energy_gauge x k]
  rw [show (∫ u,TreeFormal.billrow T _ t u ∂ T.measure G)=∫ u,(V ∘ R.restore) (T.drape u) ∂T.measure G from rfl,
      ← T.tree_gauge (V ∘ R.restore) (?_) (fun a _ x=>?_)]
  · exact Reg.compare R V hF hv
  · letI:IsFiniteMeasure (R.measure G):=inferInstance
    letI:IsFiniteMeasureOnCompacts (R.measure G):= ⟨fun _ _=> measure_lt_top _ _⟩
    exact (hF.comp R.continuous_restore).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change V (R.restore (R.act a x))=_; rw [R.act_restores, hv (a ∘ R.vertex) (fun _=>by simp)] ; rfl

lemma refers (h:Orb.PreTest O): TreeFormal.actual T (sample T O)=Orb.expectation (Orb.restrictedO O):=by
   funext t; change (∫ _, _ ∂_)/(∫ _, _ ∂_)= Orb.numerator _ t/Orb.numerator _ t
   rw [identity T t h.gauge h.continuous]
   congr 1; exact identity T t (O:=1) (fun _ _ _=>rfl) continuous_const

open Series

theorem diagram_eq (h:Orb.PreTest O):
    Bare.normalized T G (stencil T O) = TaylorWick.into (PowerSeries.mk (Orb.diag (Orb.restrictedO O))):=by
  have ht:= OrbGerm.tree T h
  have hc:Continuous (sample T O):= h.continuous.comp (R.continuous_restore.comp T.continuous_drape)
  have hw:= TreeFormal.quotients T hc ht
  rw [refers T h] at hw
  rw [stencil,sampling T O,← TreeFormal.normalized_radial T _ ht];
  exact congr_arg (fun i=>TaylorWick.into (PowerSeries.mk i)) (hw.unique (Orb.finite_formula (even_iff_two_dvd.mpr R.even) (Orb.traySpec G) h.curved))

theorem tree_independent (U:R.Tree)(h:Orb.PreTest O):
    Bare.normalized T G (stencil T O) = Bare.normalized U G (stencil U O):=by rw [diagram_eq T h,diagram_eq U h]
end BareOrb
end YM.FVA2
