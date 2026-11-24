import YM.FVAAlt2.Periodic.Rent
import YM.RegulatorIR.Oracle.Arrange
/-!
# Same ports via ledgerRow, fixed FULL torus
 Size p independent of Reel choice.Heir may be inversion but THIS theorem for full.
 Project all tie by site `p` and ONE mesh step. Script.Pert.G. Includes order-zero constants & Haar body tracked elsewhere.K here is covariance and shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Oracle.FVAAlt2.Primary
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Gauge Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Step YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
open YM.FVAAlt2.Period Rent Comparison.RG02 Comparison.RG02.Bulk
section Primary
open FreeResolvent Shell
-- padded inverse law. establish for credible K costs.
variable {I O:Type}[Fintype I][Fintype O][DecidableEq O][DecidableEq I]
lemma compress (e:I ↪ O)(R B:Matrix O O ℝ)(P:Matrix I I ℝ)(H:P= R.submatrix e e)(h:IsUnit P.det) (hu:B*pad e R=1) : Shell.rim e*B*Shell.rim e=insertion e*P⁻¹*(insertion e)ᵀ:=by
  let T := insertion e; have ht:= pin e; have hp : pad e R*T=T*P:=by unfold pad; rw [Matrix.add_mul,barred,add_zero, sliced, ← H]; change T*P*Tᵀ*T= T*P; rw [Matrix.mul_assoc, (show Tᵀ*T=1 from ht), Matrix.mul_one]
  have hv: B*T=T*P⁻¹:= by
     calc _= B*T*(P*P⁻¹):=by rw [Matrix.mul_nonsing_inv _ h,Matrix.mul_one]
          _ = _:=by rw [← Matrix.mul_assoc, Matrix.mul_assoc B,← hp,← Matrix.mul_assoc B, hu,Matrix.one_mul]
  calc
     _= Shell.rim e*(B*T)*Tᵀ:=by unfold Shell.rim; unfold T;simp only [Matrix.mul_assoc]
     _=_:= by rw [hv, ← Matrix.mul_assoc (Shell.rim _),show Shell.rim e*T=T from enters e]
end Primary
open FreeResolvent (PAC component flatten tensor active insertion fullMatrix treeMatrix)
variable {G:Gauge}(Q:KernelChoices)(P:Patch) (R : Cross P.L (TypeFace 1) (TypeFace 1)) (A D: Bed) {u s t m:ℝ} {p b: Clip}
variable (F:Hall A u s t p)(Z:P.Branches Q G) (hp:BidP P Q A D R u m)
local notation "U"=>blockQ G P.L
local notation "T"=>linksQ G
variable (c: Side){W:PathData G}{O:ChartRatio G}
local notation "f"=> c * P.L
variable (K: Comparison.RG02.Bulk.Kernel (avenue P Q c) b W O)(h:Rent.Right b W (c*P.L) A)
local notation "S"=> avenue P Q c
local notation "B" => (stemF P c)
local notation "z" => (renter P G c)
local notation "e" => insertion z
include h hp F
lemma mean (x: Bid.Dir G c) : ledgerRow U T (projectionQ P Q R G) c *ᵥ flatten x= flatten (Bid.stretch («S»:=S) B (x,fderiv ℝ (K.b B) 0 x)):=by
    let L:= installed (tileB P.L c) R; have ht:= hp.motion c; rw [Rent.initiative K A D h L ht, projRates P Q R _ c hp.rows F.pos.le hp.costV ]; ext1 i; obtain ⟨i,j,k⟩:=i; let J:= (i,j); exact congr_fun ((FreeResolvent.component_mul ( Precision.extracted S B L ) (flatten x) k).trans (Work.F04.parts_stretch B («S»:=S) L x k).symm) J
omit hp
local notation "Q₀"=> treeMatrix G S B A.metric
lemma panel (o: (S).Choices): ledgerRow U U ( hearth P Q G A F Z ) c = (insertion (renter P G c))* (show Matrix (FreeResolvent.Active G (stemF P c)) (FreeResolvent.Active G (stemF P c)) ℝ from K.covariance (stemF P c) o) *(insertion (renter P G c))ᵀ:=by
    unfold Comparison.RG02.Bulk.Kernel.covariance; rw [Rent.honest K A h B]; have hu:= savings P G; have hv:= cafe P Q G A F Z; have ht:= promised P Q G; unfold hearth; rw [Ledger.lap U U U _ (hu.lap hv) hu ht, Ledger.lap U U U _ hu hv (effects P Q G A F Z|>.choose_spec.1),physicalP P Q G]; apply compress z (fullMatrix G S A.metric) _ _ rfl
    · have hw:0<(Q₀).det := (congr_arg Matrix.det (Rent.honest K A h B o)) ▸ (K.hessian_pos B o).det_pos; exact isUnit_iff_ne_zero.mpr hw.ne'
    rw [← touches P Q G A F]; exact (ortho_cable P Q G A F Z c).2
end YM.RegulatorIR.Oracle.FVAAlt2.Primary
