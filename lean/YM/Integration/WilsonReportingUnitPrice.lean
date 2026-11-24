import YM.Integration.WilsonReportingUnitOrbit
import YM.Integration.WilsonReportingDensityProbes

/-! Reconstruct the filed reporting-date coefficient of a physical scalar
counterterm from its actual displaced Wilson densities. The finite norm
constant is fixed before the date, cutoff, period and source coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUnitPrice
open Function Set Finset Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG05Readout Address Native Many WilsonReportingUnitCells WilsonReportingUnitOrbit Trace.Physical
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {m N p b d:ℕ}

def aperture {d:ℕ} (i:Letter d) : ℝ := (Native.Cap.cost (Native.line i) 0).choose
def bound (C:Family G) (d:ℕ) : ℝ :=
  ∑ i:Letter d,WilsonReportingDensityProbes.gain C i*aperture i

theorem derivative (z:ℂ) {g:ℕ} (j:Push.Local.Probe G g) :
    ‖Germ.jet C.params j (C.path.rep N p m).p.threshold 0
      (Juniper.Caret.ratio (C.path.rep N p m) (z • liftVac C.path N p m))‖ ≤ ‖z‖ := by
  let R:=C.path.rep N p m
  let J:=R.p.threshold • j.1
  let path:=C.params.testLinks g (0:Site (C.side m p)) J
  have eq:(Juniper.Caret.ratio R (z • liftVac C.path N p m)) ∘ path=ᶠ[𝓝 0] (fun _:ℝ=>z) := by
    filter_upwards [Juniper.Caret.near_test (0:Site (C.side m p)) C.params R J] with t good
    have gas:=Activities.gas_one R.activities R.p good
    have nz:(R.eval (path t):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by
      rw [Rep.eval,gas,mul_one]
      exact (Real.exp_pos _).ne')
    change (z*(R.eval (path t):ℂ))/(R.eval (path t):ℂ)=z
    exact mul_div_cancel_right₀ _ nz
  change ‖iteratedDeriv j.2.val ((Juniper.Caret.ratio R (z • liftVac C.path N p m)) ∘ path) 0‖ ≤ ‖z‖
  rw [eq.iteratedDeriv_eq]
  by_cases e:j.2.val=0
  · simp [e]
  · simp [iteratedDeriv_const,e]

theorem price (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d p} {U:Emblems C d}
    (spine:Spine D B h b p d N V U) (above:b ≤ m) (live:m ≤ N) (aged:∀i:Letter d,C.ref (kept i) ≤ m)
    (x:Palette C d) {A:ℝ} (hA:0 ≤ A) (pay:Priced C N p m d (pulseOut (V m x)) A) :
    size x ≤ C.S.a m^d*A*bound C d := by
  obtain ⟨u,home⟩:=(spine.legal m above live).capacity0 x
  obtain ⟨v,zero⟩:=(spine.legal m above live).capacity0 0
  let cost (i:Letter d):=C.S.a m^d*A*aperture i
  have nonneg(i:Letter d):0 ≤ cost i:=mul_nonneg (mul_nonneg (pow_nonneg (C.S.a_pos _).le _) hA)
    (Native.Cap.cost (Native.line i) 0).choose_spec.1.le
  have measured(i:Letter d)(j:Push.Local.Probe G (kept i)) :
      ‖Germ.jet C.params j (C.path.rep N p m).p.threshold 0
        (Juniper.Caret.ratio (C.path.rep N p m)
         (((V m x) (Native.line i)).1-((V m 0) (Native.line i)).1))‖ ≤ cost i := by
    obtain ⟨z,hz,hb⟩:=pay (Native.line i) (aperture i) (Native.Cap.cost (Native.line i) 0).choose_spec.2
    rw [map_zero]
    change ‖Germ.jet C.params j (C.path.rep N p m).p.threshold 0
      (Juniper.Caret.ratio (C.path.rep N p m) (pulseOut (V m x) (Native.line i)-0))‖ ≤ _
    rw [sub_zero,hz]
    exact (derivative (C:=C) z j).trans hb
  have paid:=WilsonReportingDensityProbes.price h home zero aged live cost nonneg (fun i j _=>measured i j)
  rw [sub_zero] at paid
  apply paid.trans_eq
  unfold bound
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [cost]
  ring

theorem original (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d p} {U:Emblems C d}
    (spine:Spine D B h b p d N V U) (m:ℕ) (live:m ≤ N) (above:b ≤ m)
    (aged:∀i ≤ d,C.ref i ≤ m) (z:ℂ) :
    size (Many.point U (coordinate C d N z) N m) ≤ C.S.a m^d*(‖z‖/‖phase‖)*bound C d := by
  apply price h spine above live (fun i=>aged _ (Nat.sub_le _ _)) _ (div_nonneg (norm_nonneg _) (norm_nonneg _))
  exact WilsonReportingUnitOrbit.original h spine (fun i hi=>(aged i hi).trans live) m live above z

end YM.Integration.WilsonReportingUnitPrice
