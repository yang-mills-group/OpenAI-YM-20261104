import YM.FVAAlt2.Lyric.Capacity
import YM.RegulatorIR.Cluster.Poster
/-! Exponent table compatibility. Arbitrary polynomial dimensions of outputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lyric.Capacity
open Function Finset Filter Set MeasureTheory Matrix Metric Lattice
open PertExtension PertExtension.Series GaussianScore
open Next.SectorChange Next.SectorChange.Gaussian
open Diagram Diagram.Gaussian Binding Diagram.Formal PowerSeries
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff ENNReal Matrix PowerSeries
variable {I J:Type}[Fintype I][DecidableEq I] {n k m r e:ℕ}
-- green generic when budget lean r.M. Holding only actual paying.
variable [Fintype J]
variable (A:Matrix I I ℝ)(hA:A.PosDef)(D:Matrix J I ℝ)(V U:Diagram.Orders J)(w:J→ℝ)
local notation "K"=>origin A hA
local notation "d"=> direction D
local notation "L"=> Diagram.Gaussian.bond (origin A hA) (direction D)
lemma marked (h:Vacuum V)(hh:gradedSymmetric V)(ht:∀ e, Within (e+m) (U e))(hp:gradedSymmetric U):
 let T:= expo (rated (fun i=>i+2) V); let S:= fun i=>i+m; Diagram.burn K d volume (T*rated S U) w= Diagram.burn K d volume T w * flavor m w (endHeat m L (logHeat L V true) U):= by
 intro T S; let E:=endHeat m L (logHeat L V true) U
 have hv':∀ e,Within (e+(m+1)) (U e):= fun e r h=> le_trans (ht e r h) (by omega)
 have hp':endHeat (m+1) L (logHeat L V true) U=E:=by
    ext1 e;ext1 r; unfold E endHeat heated; dsimp only; symm; refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
    intro i _ he; rw [Finset.mem_range] at he; by_contra! h'; have := (Diagram.marked_cap m L V h U ht true e r i h').2; omega
 have he' (F:Orders J)(ht:∀ i,Within (i+m) (F i)): rated S F=rated (fun i=>i+m+1) F:=by ext1 i;rw [rated_v,rated_v];exact pack_extends (ht i) (Nat.le_succ _)
 have H':= Diagram.green K d volume m V U w h hh hv' hp; dsimp only at H'
 change _= _*PowerSeries.map _ (rated _ (endHeat (m+1) L _ _)) at H'
 rw [hp'] at H'; unfold flavor; change _= _* PowerSeries.map _ (rated S E); rw [he' E (Cluster.end_ranks m true ht h),he' U ht]; exact H'

lemma unmarked (h: Vacuum V)(hh:gradedSymmetric V): Diagram.burn K d volume (expo (rated (fun i=> i+2) V)) w= expo ( flavor 2 w (ceaseHeat L V true) ):= (Diagram.red K d volume V w h hh).trans (Formal.map_exp .. )

section prices
variable {E:Type*}{q:PowerSeries ℝ} {y:E}{v:ℕ→E→ℝ}
variable (h:∀ i≤r,v i y= coeff i q)
include h
lemma paint_pow (he:e ≤ r)(n:ℕ): PertExtension.Series.Zone.TaylorPow v n e y=coeff e (q^n):=by
 induction n generalizing e with
 | zero => simp [PertExtension.Series.Zone.TaylorPow]
 | succ n ih=> unfold PertExtension.Series.Zone.TaylorPow PertExtension.Series.Zone.mul; rw [pow_succ,coeff_mul]; refine sum_congr rfl (fun p hp=>?_ ); have hp:= mem_antidiagonal.mp hp; rw [ih (by omega),h _ (by omega)]
-- Radial.expsum requires [NormedAddCommGroup E]?
lemma painter [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E](he:e≤r): coeff e (Formal.expo q)=PertExtension.Series.Radial.expsum v e e y:=by
   unfold Formal.expo Formal.truncP PertExtension.Series.Radial.expsum; rw [coeff_mk,map_sum]; exact sum_congr rfl (fun p _=> by rw [coeff_smul,paint_pow h he]; rfl)
end prices
end YM.RegulatorIR.FVAAlt2.Lyric.Capacity
