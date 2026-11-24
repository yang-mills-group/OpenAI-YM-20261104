import YM.Integration.WilsonPositionProgramTrialPublicCellPulse
import YM.Integration.WilsonIndependentMatchedTopReceipt

/-! Every jet used by the reprinted original group dose is continuous in its true subcell displacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalBufferedCellProbe
open Function Finset Lattice RG Wilson Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Cosmos
open WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Embroider WilsonCoeffUV.Mer
open WilsonPositionProgramTrialPublicCellPulse (placed)
open WilsonIndependentFittedExteriorProfile (home jet)
open scoped Classical BigOperators Topology
variable {D:ℕ}

theorem coordinate (T:Rarity D)(x y σ:ℝ)(sp:0<σ)(o:CellR)(z:Cover)(a:Knob D)(b:Chamber):
    Continuous fun ξ:Point4=>(wheelC x y z (placed T x y σ sp o ξ).ψ o).val a b:=by
  let gone:=fun ξ:Point4=>σ⁻¹ • (-(-(y • o.val)-x • ξ)+address x y o z b.val)
  have smooth:Continuous (fun p:Point4=>crease T.ψ a.2 p):=
    continuous_iff_continuousAt.mpr (fun p=>Analysis.iterD (x:=p)
      (scribble T.ψ (Nat.le_of_lt_succ a.1.isLt)).contDiffAt (Embroider.dot ∘ a.2))
  have motion:Continuous gone:=by unfold gone;fun_prop
  have paid:Continuous (fun ξ:Point4=>x^a.1.val*(σ⁻¹^4*(σ⁻¹^a.1.val*crease T.ψ a.2 (gone ξ)))):=
    continuous_const.mul (continuous_const.mul (continuous_const.mul (smooth.comp motion)))
  apply paid.congr
  intro ξ
  change _=crease (sonal x y o z (placed T x y σ sp o ξ).ψ) a.2 b.val
  rw [currentP _ _ _ _ _ _ (Nat.le_of_lt_succ a.1.isLt),WilsonPositionProgramTrialPublicCellPulse.placed,jet _ _ sp _ _ (Nat.le_of_lt_succ a.1.isLt)]

theorem jewel {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(cut:d<D)(T:Rarity D)(x y σ:ℝ)(sp:0<σ)
    (o:CellR)(z:Cover)(a:Alma F):
    Continuous fun ξ:Point4=>jewelBloom cut a (wheelC x y z (placed T x y σ sp o ξ).ψ o):=by
  exact coordinate T x y σ sp o z _ zeroC

theorem product {G:Gauge}{n:ℕ}{d D:Fin (n+1)→ℕ}{F:(i:Fin (n+1))→Labels.Frame G (d i)}
    (cut:∀i,d i<D i)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)
    (o:Fin (n+1)→ CellR)(z:Fin (n+1)→ Cover)(a:(i:Fin (n+1))→Alma (F i)):
    Continuous fun ξ:Fin (n+1)→Point4=>∏i,drumB (d i) (x i)*
      jewelBloom (cut i) (a i) (wheelC (x i) y (z i) (placed (T i) (x i) y σ sp (o i) (ξ i)).ψ (o i)):=by
  apply continuous_finsetProd
  intro i _
  exact continuous_const.mul ((jewel (cut i) (T i) (x i) y σ sp (o i) (z i) (a i)).comp (continuous_apply i))

end YM.Integration.WilsonOriginalPublicNodalBufferedCellProbe
end
