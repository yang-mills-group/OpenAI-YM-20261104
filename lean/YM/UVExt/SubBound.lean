import YM.UVExt.SubtotalAnalytic
import YM.UVExt.IntegratedRay

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay
open RG Wilson Lattice Tree Pressure ConnectedActivityE6 Coat Raw Mask Pulse Itinerary Poll Pond Gaussian MeasureTheory Measure
open Filter Set Function Metric Push.AbsoluteSums Matter
open scoped Topology BigOperators Classical ENNReal

variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
variable (X:Coat T F) (R:Rep G f) (t:ℝ) (Ñ:Precision.ChartRatio G) (l : Finset ℕ) (d:ℕ) (W:ℝ) (p:Molecule S)
variable {μ cst:ℝ} {L:Side} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {o:Target.Order G W}
open Finset
lemma wages_cap (w:Iris X R d p) : Traces.wage (people p) (wages X R t Ñ l d W p w) ≤ fees X R d p := by
    unfold Traces.wage people fees; rw [Finset.sum_disjSum,sum_singleton]; apply add_le_add le_rfl (sum_le_sum _); intro i hi
    rcases i with A|u|u|u <;> simp only [wages,markTax, shade, capsule, Sum.elim]
    · rfl
    · change 0 ≤ 1; omega
    · split <;> simp [Primitive.tax]
    change 0 ≤ 1; omega

variable (hk : X.width=o.K) (hx : 0<R.beta) (hX : X.manifest)
    (I:Set ℝ) (hI:IsOpen I) (hd:I⊆Ioi 0)
local notation "A" => allow X R W (μ:=μ) (cst:=cst) (Q:=Q) (L:=L) (o:=o)
local notation "m" => quarry X R Q.halo p
local notation "g" => tiltedTerm X R o.a Q.table l Q.halo W p
variable (admitReal: ∀ r∈I,Nonempty (allow X R W (μ:=μ) (cst:=cst) (Q:=Q) (L:=L) (o:=o) r))
include admitReal hk hx hX hI hd
lemma analytic_subtotal : AnalyticOnNhd ℂ (subtotal X R o.a Q.table l Q.halo W p) (Complex.re⁻¹' I) := by
 let H (r) (he:r∈I):A r:=(admitReal r he).some
 by_cases hh : I.Nonempty
 · obtain ⟨u,hu⟩:=hh
   obtain ⟨r,hr,h⟩:=Metric.isOpen_iff.mp hI u hu
   let s:=u+r/2; have hs:s∈I := h (by simpa [s,mem_ball, Real.dist_eq,abs_of_pos,hr]); have hsI:=hd hs
   exact Traces.integrating m g (term_m X R l W p hk hx (hd hu) hsI (H u hu) (H s hs) (by dsimp [s]; linarith) ·)
      (people p) (fees X R Q.halo p) (fun w=>⟨_,fun z _=> printed_sum ..,wages_cap ..⟩) I hI hd (fun z hz=> (tilted_real X R _ _ _ hk hx hX (hd hz) (H z hz)).1)
 rw [Set.not_nonempty_iff_eq_empty.mp hh]; simp
lemma quoted_subtotal {z:ℂ} (hz : z.re∈I) (admitAt : A z.re): ‖subtotal X R o.a Q.table l Q.halo W p z‖ ≤ (‖z‖/z.re)^ fees X R Q.halo p * ∏ i∈p,admitAt.text i := by
 obtain ⟨r,hr,h⟩:=Metric.isOpen_iff.mp hI _ hz
 let s:=z.re+r/2; have hs:s∈I := h (by simpa [s,mem_ball, Real.dist_eq,abs_of_pos,hr]); have hsI:=hd hs
 exact angular_bill (r:=0) X R l W p hk hx hX z (hd hz) hsI admitAt (admitReal s hs).some (by dsimp [s]; linarith)
end YM.UVExt.EnergyRay
