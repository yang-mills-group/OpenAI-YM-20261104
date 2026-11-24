import YM.Integration.WilsonOriginalOneColor
import YM.Integration.WilsonOriginalPointDilation
import YM.QuadraticLocal.Lamps

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOneColorGallery
open Function Filter Finset Set Lattice Wilson RG Ac Marker QuadraticLocal MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Push Push.Corrected Push.AbsoluteSums
open QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached
open Multi WilsonOriginalOneColor
open scoped Classical BigOperators Topology
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {T ι:Type} {o:V→Site n} {p:BudgetPoint} {P:Rep G n}

def gallery (v:V) (A:Gallery T ι o P R):Gallery T (seats v A.E) o P R:=⟨lamps v A.E,hard v A.K⟩

omit [Fintype V] in
theorem signal (v:V) (A:Lamps T ι G p o R) (i:ι) (t:T) (U:Config G n):
    cut v (A.frame i t U)=(seats v A).indicator (fun j=>A.frame j t U) i:=by
  change Multi.dilation R (turn v) (Poly.send (A.mode i) _) = _
  rw [Multi.dilation_send,coefficient]
  by_cases use:i∈seats v A
  · have yes:visible v (A.mode i):=use
    rw [Set.indicator_of_mem use,if_pos yes,one_mul]
    rfl
  · have no:¬visible v (A.mode i):=use
    rw [Set.indicator_of_notMem use,if_neg no,zero_mul]
    ext1 s;simp

omit [Fintype V] in
theorem log (v:V) (A:Lamps T ι G p o R) (t:T) (U:Config G n) (sum:Summable (fun i=>A.frame i t U)):
    (lamps v A).log t U = cut v (A.log t U):=by
  change (∑' i:seats v A,A.frame i.val t U)=
    WilsonOriginalPointDilation.act (turn v) (∑'i,A.frame i t U)
  rw [_root_.tsum_subtype (seats v A) (fun i=>A.frame i t U),(WilsonOriginalPointDilation.act (turn v)).map_tsum sum]
  exact tsum_congr fun i=>(signal v A i t U).symm

omit [Fintype V] in
theorem load (v:V) (A:Gallery T ι o P R) (s:Finset ℕ) (t:T) (U:Config G n):
    packet P.activities P.p ((gallery v A).K.hard t) U s= cut v (packet P.activities P.p (A.K.hard t) U s):=by
  unfold packet
  split
  · rw [map_prod];rfl
  · exact (map_zero _).symm

omit [Fintype V] in
theorem gas (v:V) (A:Gallery T ι o P R) (t:T) (U:Config G n)
    (sum:Summable (packet P.activities P.p (A.K.hard t) U)):
    (gallery v A).gas t U=cut v (A.gas t U):=by
  change _=WilsonOriginalPointDilation.act (turn v) (∑'i,packet P.activities P.p (A.K.hard t) U i)
  rw [(WilsonOriginalPointDilation.act (turn v)).map_tsum sum]
  exact tsum_congr fun s=>load v A s t U

omit [Fintype V] in
theorem paid (v:V) (A:Gallery T ι o P R) {w:V→ℝ} (pos:∀i,0<w i) {a e k:ℝ}
    (receipt:A.Pays w a e k):(gallery v A).Pays w a e k:=
  ⟨regular v _ receipt.budget,WilsonOriginalOneColor.paid v _ pos receipt.wages⟩

theorem original (v:V) (A:Gallery T ι o P R) {w:V→ℝ} (pos:∀i,0<w i) {a e k:ℝ}
    (ha:0≤a) (receipt:A.Pays w a e k) (t:T) (U:Config G n):
    (gallery v A).density t U=cut v (A.density t U):=by
  have summed:=receipt.budget.sums ha pos t U
  have nil':=(A.E.quiet_of_hasSum t U summed)
  change (Complex.ofReal (Real.exp (P.exponent U))) •
    (Poly.pass ((lamps v A.E).log t U)*(gallery v A).gas t U)=
      cut v (Complex.ofReal (Real.exp (P.exponent U)) • (Poly.pass (A.E.log t U)*A.gas t U))
  rw [map_smul,map_mul,log v A.E t U summed,gas v A t U (A.K.packet_summing receipt.wages ha pos t U),
      Multi.pass_map _ _ nil' ((quiet v _).trans nil')]

end YM.Integration.WilsonOriginalOneColorGallery
end
