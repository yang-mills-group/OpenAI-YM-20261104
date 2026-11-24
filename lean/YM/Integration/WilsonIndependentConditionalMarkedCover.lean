import YM.Integration.WilsonIndependentConditionalVerse
import YM.WilsonCoeffUV.Ward.AxisColor

/-! Fixed marked tensors of the normalized conditional on ordinary tori and its
authenticated cover limit. The finite reader differentiates the actual diagram. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalMarkedCover
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open WilsonCoeffUV.Blue Embroider Embroider.Canvas PowerSeries
variable {G:Gauge}

def tensor {U:Type} (V:Ink U)(i r:ℕ)(z:Fin r→U):ℝ:=
   (r.factorial:ℝ)⁻¹ * tally r z (coeff i V)

theorem reads {U:Type}[Fintype U]{k:ℕ}{F:ℕ→Gen ℝ U}(span:shellK k F)(pure:∀ i,Pure (F i))(i r:ℕ):
    tensor (Blue.flash F) i r=F i r:=by
  funext z
  have finite:=finite_shell span i
  let n:=max (r+1) finite.choose
  have hr:r<n:=Nat.lt_of_lt_of_le (Nat.lt_succ_self r) (le_max_left ..)
  unfold tensor Blue.flash
  rw [coeff_mk,visible (finite.choose_spec.mono (show finite.choose≤n from le_max_right ..)),map_sum,
    Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hr) (fun j _ hj=>pale hj (F i j) (pure i j) z),Blue.rotate _ (pure i r)]
  rw [nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast r.factorial_ne_zero),one_mul]

def report (A:Levels G)(Ñ:ChartRatio G)(m N k:ℕ)(Z:Era G ℝ)(c:Side):Ink (Woods G c):=
  let P:=loose A m;let S:=mStep A c m;let F:=repeatF S
  let H:=freeForms A N (m+1);let Q:=roam A N m c
  let V:=(story A Ñ N (m+1)).1 (c*P.L)
  redo (ratioHigh A Ñ N m) (projectZero (WilsonIndependentConditionalDiagramResponse.response S F H Q Ñ V (Z.1 (c*P.L)) k))

theorem finite (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth (k+1) Z)(c:Side)(i r:ℕ):
    tensor (report A Ñ m N (k+1) Z c) i r=(verseI A Ñ m N (k+1) Z).1 c i r:=by
  have chart:=Auth.verse A finer simple ratio source
  rw [show report A Ñ m N (k+1) Z c=Blue.flash ((verseI A Ñ m N (k+1) Z).1 c)
       from WilsonIndependentConditionalVerse.original A simple ratio finer c Z source]
  exact reads (chart.span c) (chart.pale c) i r

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth (k+1) Z)(i r:ℕ):
    Bends 0 (fun c=>tensor (report A Ñ m N (k+1) Z c) i r) ((verseI A Ñ m N (k+1) Z).2 i r):=by
  simpa only [finite A simple ratio finer Z source] using (Auth.verse A finer simple ratio source).wing i r

end YM.Integration.WilsonIndependentConditionalMarkedCover
