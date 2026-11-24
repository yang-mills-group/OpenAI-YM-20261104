import YM.Juniper.Caret.Traverse
import YM.RG05Readout.Address.Size

/-! Recover the reporting palette from a fixed finite family of measured
derivatives of the actual normalized Wilson densities. The probe selection
and its numerical constants precede every period, cutoff and pair of tapes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingDensityProbes
open Function Filter Set Lattice Wilson RG Source Labels Push.Local Next.Foundations
open RG05Readout Address Native Extra.Histories Trace.Physical
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {d:ℕ} {n:Side}

theorem physical (F:Labels.Frame G d) (o:Site n) (B:SectionData F) (H:Hol G)
    (R:Rep G n) (Q:Coefficient F n) (sound:B.Sound H) (fit:Juniper.Caret.Sits F B n)
    (order:d ≤ R.p.order) (power:d ≤ R.p.power) (format:Q.Format o H R)
    {κ cash:ℝ} (budget:Q.remBound o R κ cash) :
    Juniper.Caret.Pass F o H R (Q.density o B R) (Germ.projection F H R.p.threshold o Q) := by
   have he:= Juniper.Caret.bills F o B H R Q fit format budget order sound
   let x:= R.p.threshold
   have hS:= Germ.vector_summable F H format budget order power
   have hU:=budget
   obtain ⟨a,b,-,hb,hB,-,⟨qA,hkA,hA⟩,-⟩:=hU
   have budget':Summable qA:= Summable.of_nonneg_of_le (fun i=> (hA i).1) (fun i=> R.p.loMass _ _ (hA i).1) hkA.2.1
   let f:= B.places (F.scaled x⁻¹ Q.x) o
   have sourceJet : JetTest H o (F.coords.symm (F.scaled x⁻¹ Q.x)) f:=by
     have hT:= placed_reads (H:=H) B o fit sound (F.scaled x⁻¹ Q.x); rwa [Reads,if_pos (nonwrapping_placement B o fit)] at hT
   refine ⟨fun j=> ⟨(he.listens j).1,?_⟩⟩
   let v:= j.2.val; let A:=Push.Local.runProbe F j; unfold Germ.projection
   rw [map_add, ContinuousLinearMap.map_tsum _ hS]; simp_rw [Germ.vector, Germ.charged F H R.p.threshold (Germ.computed H (format.smooth _) o order)] -- dot simpl maybe
   let z:=x • j.1; let p:=H.testLinks d o z; let K(i):= (Q.regular i) ∘ p; let W(t):= ∑' i,K i t; let Z:=Juniper.Caret.ratio R (Q.density o B R)
   obtain ⟨hZ,sound'⟩ := Juniper.Caret.journey R.p o H Q.regular order format.smooth budget' hA z;
   have hv: Z∘p=ᶠ[𝓝 0] f∘p+W := (Juniper.Caret.near_test o H R z).mono fun i hi=> Juniper.Caret.unveil F o B H R Q _ hi sound
   have hj:= Nat.le_of_lt_succ j.2.isLt; have hx:= Juniper.Caret.appears F o H R j sourceJet; rw [F.coords.apply_symm_apply,F.scaled_inv (show R.p.threshold ≠0 from R.p.threshold_pos.ne')] at hx
   change A Q.x + ∑' i, iteratedDeriv v (K i) 0=_
   rw [hv.iteratedDeriv_eq, show ∑' i,iteratedDeriv v (K i) 0 = iteratedDeriv v W 0 from (sound' v hj).tsum_eq, hx, iteratedDeriv_add _ (show ContDiffAt ℝ (↑(j.2.val)) W 0 from hZ.of_le (Nat.cast_le.mpr hj)) ]
   exact (sourceJet z).1.of_le (Nat.cast_le.mpr hj)

variable {C:Family G} (hC:C.Makes) {N per m:ℕ}
include hC in
theorem observed {T:Tape G (C.side m per)} {x y:Palette C d} {κ c:ℝ}
    (issued:Printed C d (C.path.rep N per m) 0 κ T x y c) (i:Letter d)
    (aged:C.ref (kept i) ≤ m) (live:m ≤ N) :
    Juniper.Caret.Pass (C.labels.level (kept i)) 0 C.params (C.path.rep N per m)
      (T (Native.line i)).1 (y i) := by
  rcases issued with @⟨V,W,v,b,H,format,cost,rfl,rfl,rfl,_⟩
  rw [together_line V W H]
  obtain ⟨order,power⟩:=GermGraph.dimensions (kept i) N per m hC aged live
  exact physical _ _ _ _ _ (V i) (hC.sections _) (hC.places _ m per aged)
    order power (format i) (cost i)

def tests (C:Family G) {d:ℕ} (i:Letter d) : Finset (Probe G (kept i)) :=
  (probe_budget (C.labels.level (kept i))).choose

def gain (C:Family G) {d:ℕ} (i:Letter d) : ℝ :=
  (probe_budget (C.labels.level (kept i))).choose_spec.choose

include hC in
/-- A finite numerical bill for a signed difference in the *genuine* printed
report. Only the actual, section-normalized density and its finite jet data
enter the test. Both tapes may contain the full summable signed remainder. -/
theorem price {P Q:Tape G (C.side m per)} {x y x' y':Palette C d} {κ c c':ℝ}
    (printed:Printed C d (C.path.rep N per m) 0 κ P x y c)
    (booked:Printed C d (C.path.rep N per m) 0 κ Q x' y' c')
    (aged:∀i:Letter d,C.ref (kept i) ≤ m) (live:m ≤ N) (bill:Letter d→ℝ)
    (nonneg:∀i,0 ≤ bill i)
    (charged:∀i:Letter d,∀ j∈tests C i,
      ‖Germ.jet C.params j (C.path.rep N per m).p.threshold 0
        (Juniper.Caret.ratio (C.path.rep N per m) ((P (Native.line i)).1-(Q (Native.line i)).1))‖ ≤ bill i) :
    size (y-y') ≤ ∑ i:Letter d,gain C i*bill i := by
  rw [bill_group]
  apply Finset.sum_le_sum
  intro i _
  have matched:=(observed hC printed i (aged i) live).sub (observed hC booked i (aged i) live)
  apply (probe_budget (C.labels.level (kept i))).choose_spec.choose_spec.2 _ (bill i) (nonneg i)
  intro j tested
  change ‖runProbe (C.labels.level (kept i)) j (y i-y' i)‖ ≤ bill i
  rw [(matched.listens j).2]
  exact charged i j tested

end YM.Integration.WilsonReportingDensityProbes
