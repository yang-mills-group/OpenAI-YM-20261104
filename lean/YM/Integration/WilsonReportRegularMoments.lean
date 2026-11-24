import YM.Integration.WilsonReportEarlyFlags
import YM.Integration.WilsonReportMomentDifference

/-! The authentic periodic fine moment and its full regular coarse
counterpart for each occupied component of the finite physical report.
Pointwise control is used only on the regular columns; rare signed
sector differences retain their original integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportRegularMoments
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26
open RG12 RG17 RG17.Panoramic SharpGram Next.UVStress Extra.Histories
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol OPE.Strobe.Panoramic
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}

private theorem scale (C : Family G) (d k N p : ℕ) (v : C.label d) :
    Spindle.paid C d k N p v=(C.S.a k^d)⁻¹*quota C d k N p v := by
  unfold Spindle.paid Price.awake
  rw [Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos k).le]
  rfl

private theorem rescale {a b v b₀ A : ℝ} {d t : ℕ} (ha : 0<a) (hb : 0<b)
    (h : v ≤ (b/a)^d * (b₀^t)^(d+1) * (a^d*A)) :
    (b^d)⁻¹ * v ≤ b₀^(t*(d+1))*A := by
  calc
    _ ≤ (b^d)⁻¹*((b/a)^d*(b₀^t)^(d+1)*(a^d*A)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hb.le _))
    _ = _ := by rw [div_pow,←pow_mul]; field_simp

/-- The true cost at the deeper berth. It keeps the reverse transport
factor (a_m/a_k)^(d+1); the original envelope bounds that ratio by H_k^t. -/
theorem transported (L : Layout F) (E : OPE.Services R.family f S) (r : ℝ) {d k N p t : ℕ}
    (w : R.family.label d) (grade : R.family.ref d≤L.level r) (deep : L.level r≤k) (cut : k≤N)
    (zoom : R.family.S.a (L.level r)/R.family.S.a k≤R.family.path.levels.clock.hatBeta k^t) :
    Spindle.paid R.family d k N p (atRef L d r (N,p) w) ≤
      R.family.path.levels.clock.hatBeta k^(t*(d+1))*mass R.family d (L.shift d r w) := by
  let C := R.family
  let y := atRef L d r (N,p) w
  let m := L.level r
  let H := C.path.levels.clock.hatBeta
  have hm := C.S.a_pos m
  have hβ := C.path.levels.fits.delayed k
  have old : quota C d m N p y=(C.S.a m)^d*mass C d (L.shift d r w) := by
    have paid := WilsonReportRegulatedSmear.reference (N:=N) (p:=p) L r d w grade (deep.trans cut)
    change Spindle.paid C d m N p y=mass C d (L.shift d r w) at paid
    rw [scale] at paid
    rw [←paid]; field_simp
  have tr := RG17.podQuota (i:=(N,p)) E zoom (one_le_pow₀ hβ.le) F.room.cutoff y
    grade (grade.trans deep) (deep.trans cut) cut
  rw [old] at tr
  rw [scale]
  exact rescale hm (C.S.a_pos k) tr

/-- The physical regular column on each coarse gauge configuration, with
the polynomial coefficient bought before any cutoff, torus or position. -/
theorem regular (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (L : Layout F) (E : OPE.Services R.family f S) (r : ℝ) {d k N p t : ℕ} (w : R.family.label d)
    (grade : R.family.ref d≤L.level r) (zero : R.family.ref 0 < k) (deep : L.level r≤k) (cut : k < N)
    (zoom : R.family.S.a (L.level r)/R.family.S.a k≤R.family.path.levels.clock.hatBeta k^t)
    (x : Site (R.family.side k p)) (U : Config G (R.family.side k p)) :
    ‖regularRead R.family d k N p (atRef L d r (N,p) w) x U‖ ≤
      3*(R.family.path.levels.clock.hatBeta k^(1+t*(d+1))*mass R.family d (L.shift d r w)) := by
  obtain ⟨citizen,book⟩ := WilsonReportCitizenRun.on_run hG W funding subsidy
  obtain ⟨σ,χ,tune⟩ := OPE.Yarn.enroll citizen.toSharper R.makes hG
  have fare := transported (p:=p) L E r w grade deep cut.le zoom
  have true := ((enamelCost tune citizen x (grade.trans deep) zero cut _ fare).2.2 U).1
  apply true.trans
  rw [pow_add,pow_one,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (book.money.present k) ((paid_pos ..).trans fare)) (by norm_num)

/-- Exact microscopic source in the actual fine Wilson scene at the
ancestor placement, with the real finite-cutoff reference labels. -/
def fine (L : Layout F) {n : ℕ} (d : Fin n→ℕ) (w : (j:Fin n)→R.family.label (d j))
    (r : ℝ) {N k p : ℕ} (cut : k≤N) (x : Fin n→Site (R.family.side k p)) :
    Fin n → Config G (R.family.side N p) → ℂ :=
  fun j=>abrade R.family (atRef L (d j) r (N,p) (w j)) N k p (x j) cut

/-- Complete regular fields on one common coarse sample, including all
their original signs and color components. -/
def coarse (L : Layout F) {n : ℕ} (d : Fin n→ℕ) (w : (j:Fin n)→R.family.label (d j))
    (r : ℝ) {N k p : ℕ} (x : Fin n→Site (R.family.side k p)) : Fin n → Config G (R.family.side k p) → ℂ :=
  fun j=>regularRead R.family (d j) k N p (atRef L (d j) r (N,p) (w j)) (x j)

/-- Each signed difference is the genuine joint Wilson moment minus the
joint regular moment. Integrability is obtained from the positive original
vacuum and the paid signed difference. -/
theorem identity (L : Layout F) {n : ℕ} {Γ : Census (Fin n)} (d : Fin n→ℕ) (w : (j:Fin n)→R.family.label (d j))
    (r : ℝ) {N k p : ℕ} (cut : k≤N) (x : Fin n→Site (R.family.side k p)) (s : Γ.Mode)
    (live : Integrable (gapTag R N s x (shutter R L d r N p w)) (OPE.Therm.scene R.family.path N p k)) :
    let μ := OPE.Therm.scene R.family.path N p k
    let Z := fineJob (coarse L d w r (N:=N) x) s.val
    Integrable Z μ ∧ moment (R.family.beta N p) (fineJob (fine L d w r cut x) s.val) - ∫ U,Z U ∂μ =
      ∫ U,gapTag R N s x (shutter R L d r N p w) U ∂μ := by
  let v := fun j=>atRef L (d j) r (N,p) (w j)
  let z := shutter R L d r N p w
  let μ := OPE.Therm.scene R.family.path N p k
  let P := fun U=>pullDimes z (p:=p) (N:=N) (attachV R k x N) s k U / (boardMass R.family N p k U:ℂ)
  let Z := fineJob (coarse L d w r (N:=N) x) s.val
  let Δ := gapTag R N s x z
  have facts := sceneRoot R d v x cut s
  letI : IsProbabilityMeasure μ := OPE.Therm.probability (p:=p) R.makes.wilson cut
  have hp : Integrable P μ := facts.1.integrableC _
  have hz : Z=P-Δ := by
    funext U
    change Z U=P U-(P U-Z U)
    abel
  have emit : Integrable Z μ := hz.symm ▸ hp.sub live
  have joint : ∫ U,P U ∂μ = moment (R.family.beta N p) (fineJob (fine L d w r cut x) s.val) := facts.2
  dsimp only
  refine ⟨emit,?_⟩
  rw [←joint]
  exact (integral_sub hp emit).symm

end YM.Integration.WilsonReportRegularMoments
end

