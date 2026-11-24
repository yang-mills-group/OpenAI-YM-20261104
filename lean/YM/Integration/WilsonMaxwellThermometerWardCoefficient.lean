import YM.Integration.WilsonMaxwellThermometerWardPupil

/-! Reading the two-curvature coefficient on the true inversion pupil.
The running-law zero face, the divisor, and the Cartesian component are
taken at the same finite torus before extracting its radial coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardCoefficient
open Function Filter Set Finset MeasureTheory Lattice Labels Source Wilson
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.Series
open Chart Series.Radial Series.Tested WilsonMaxwellThermometerWardPupil
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side}

theorem addition (f g:Config G n→ℝ) (hf:Continuous f) (hg:Continuous g):
    preExpectation (f+g)=preExpectation f + preExpectation g := by
  funext t
  unfold preExpectation
  rw [Pi.add_apply, ←add_div]
  apply congrArg (fun x:ℝ=>x/preNum (G:=G) (n:=n) 1 t)
  unfold preNum
  have hw:Continuous (preDensity (G:=G) (n:=n) t) := Real.continuous_exp.comp (((energy_cont.div_const 2).neg).div_const (t^2))
  have hu:Continuous (liftLinks : (OEdge n→G.El)→Config G n):=lift_cont _
  simp only [Pi.add_apply,add_mul]
  exact integral_add (((hf.mul hw).comp hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hg.mul hw).comp hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

variable {d:ℕ} {F:Frame G d} (C:SectionData F) (c:F.Coeff) (L:ℂ→L[ℝ]ℝ)
    (o:Site n) {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C)

include sound pop in
theorem admitted (s:Finset F.Index):PreTest (selected C c L o s):=by
  have h(i):= (pre_field C sound pop i o).1
  have hc:Continuous (selected C c L o s) := continuous_finsetSum _ (fun i _=>continuous_const.mul (h i).continuous)
  refine ⟨?_,⟨hc.comp continuous_links,?_⟩,hc⟩
  · intro u hu U
    apply Finset.sum_congr rfl
    intro i _
    rw [(h i).gauge u hu U]
  · change ContDiffAt ℝ ∞ (fun x:Dir G n=>∑ i∈s, L (c i)*fieldAt C i o (representative x)) 0
    exact ContDiffAt.sum fun i _=>contDiffAt_const.mul (h i).curved.germ

local notation "head" => selected C c L o (next (F:=F))
local notation "high" => selected C c L o (later (F:=F))
local notation "raw" => selected C c L o (active (F:=F))

include sound pop in
theorem extraction (even:Even n.val) (simple:G.Simple):
    diagonalWith (tray G) (restrictedO raw) 2 = diagonalWith (tray G) (restrictedO head) 2 ∧
    Tendsto (preExpectation raw) Tested.germ (𝓝 0) ∧
    Tendsto (fun t:ℝ=>t⁻¹^2*preExpectation raw t) Tested.germ
      (𝓝 (diagonalWith (tray G) (restrictedO head) 2)) := by
  have here:=admitted C c L o sound pop
  have first:=before_tree_formula even (traySpec G) (here active)
  have value:raw=head+high:=funext (WilsonMaxwellThermometerWardPupil.split C c L o simple)
  have added:=addition head high (here next).continuous (here later).continuous
  have split:diagonalWith (tray G) (restrictedO raw)=
      diagonalWith (tray G) (restrictedO head)+diagonalWith (tray G) (restrictedO high):=by
    apply first.unique
    rw [value,added]
    exact (before_tree_formula even (traySpec G) (here next)).add (before_tree_formula even (traySpec G) (here later))
  obtain ⟨atTwo,atThree⟩:=costs C c L o sound pop simple
  have noHigh:=diag_down (traySpec G) (here later).curved atThree even 2 (by decide)
  have downstairs:=diag_down (traySpec G) (here active).curved atTwo even
  have priced:diagonalWith (tray G) (restrictedO raw) 2=diagonalWith (tray G) (restrictedO head) 2 := by
    simpa only [Pi.add_apply,noHigh,add_zero] using congrFun split 2
  refine ⟨priced,?_,?_⟩
  · simpa only [downstairs 0 (by decide)] using first.tendsto_first
  · simpa only [Nat.add_zero,priced,smul_eq_mul] using (first.shift downstairs).tendsto_first

end YM.Integration.WilsonMaxwellThermometerWardCoefficient
