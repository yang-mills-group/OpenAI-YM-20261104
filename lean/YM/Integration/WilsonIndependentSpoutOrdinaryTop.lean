import YM.Integration.WilsonIndependentSpoutOrdinaryPlate
import YM.Integration.WilsonIndependentSpoutWilsonJets
import YM.RegulatorIR.Oracle.Life

/-! At the common bare opening the enrolled bulk plaquettes read the Spout
top on any periodic field. The rank-zero vacuum normalizer is separate. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrdinaryTop
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Binding RegulatorIR.Laplace RegulatorIR.Prim RegulatorIR.Oracle
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Halo
open PowerSeries PertExtension.Series.Radial WilsonCoeffUV.Blue RegulatorIR.Ledger
open WilsonIndependentSpoutOrdinaryPlate
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{n:Side}

theorem read (y:TreeVars G n)(e:ℕ):
    MvPolynomial.eval y (totalR (topW G n e)) =
      coeff (2+e) (tale (fun t:ℝ=>eWilson (t • y))) := by
  have h:topW G n=sprig (eWilson (G:=G) (c:=n)) 2:=by
    funext j r;unfold topW lop
    split_ifs with k
    · subst r;rw [sprig,shine_dark (by omega:2+j≠0)]
    · rfl
  have hf:ContDiffAt ℝ ∞ (eWilson (G:=G) (c:=n)) 0:=W_green.of_le (by simp)
  rw [h,sprig,visible_shine,←Blue.jet_apply,rayon,lore hf y]
  simp only [inscription,coeff_mk]
  rfl

theorem original {X:Type}{M:X→ℕ}(t:Page M→Scale)(w:X)
    (bare:t (Page.opening M w)=Clocks.flat)(y:TreeVars G n)(e:ℕ)(pos:0<e):
    (∑ p:Face (Per n),drums (Circuit.mural G t w (base p) e) (e+2) (sample y)) =
      -MvPolynomial.eval y (totalR (topW G n e)) := by
  have h:=Circuit.serene G t w
  rw [bare] at h
  rw [WilsonIndependentSpoutOrdinaryPlate.original h y e pos,read,Nat.add_comm 2]

end YM.Integration.WilsonIndependentSpoutOrdinaryTop
