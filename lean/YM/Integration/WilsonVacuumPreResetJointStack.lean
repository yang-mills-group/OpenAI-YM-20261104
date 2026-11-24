import YM.Integration.WilsonVacuumPreResetJointSite

/-! The whole finite list elected by the earlier Wilson action is read with
its own coefficients. The signed path and spatial sums are taken on each
physical torus. Their charge depends only on the issued width, face budget,
orders and number of roots used on this torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointStack
open Stationary Function Filter Finset Lattice RG Wilson Tree Pressure Gauge Precision
open Push Push.Uniform Push.AbsoluteSums ConnectedActivityE6 Coat Control Blaze
open AnalyticNext.QuarticMatch.Estimate RG01.Sounder Logfee Work.G05
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonLimitConstruction
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw WilsonVacuumPreResetJointSite
open OriginalMarkedRunAction
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def entry {k : ℕ} (A : ℕ → Atom G k) (P : Finset (Bond c)) (X : Coat T F)
    (d : ℕ) (x : Site f) (v : Arguments G c f) : ℝ :=
  Patch.average fun s : Signed => developed P X d
    (fun U => ∑' i, (A i).unmasked (pull s 0 U) x) v

def sheet (Z : SeriesA G) (u : ℝ) (P : Finset (Bond c)) (X : Coat T F)
    (d : ℕ) (x : Site f) (v : Arguments G c f) : ℝ :=
  (Z.map fun a => u^(a.grade-a.rise)*entry a.cells P X d x v).sum

def rowBill (G : Gauge) (σ C : ℝ) (k j r : ℕ) (t : ℝ) : ℝ :=
  let h := j+(r+2)+1
  let u := composeCost h ((1+(2:ℝ)^h/Work.F02.radius σ)^h) (linkFee G h)*|Work.F02.slotConst G| ^k
  j.factorial*(C*u)*(1+((1+1)*1):ℝ)^j*t^(r+3)

def charge (Z : SeriesA G) (σ C ρ u : ℝ) (j r : ℕ) (t : ℝ) : ℝ :=
  (Z.map fun a => |ρ*u^(a.grade-a.rise)| * rowBill G σ C (a.rise+2) j r t).sum

theorem measured (Z : SeriesA G) {σ C : ℝ} (width : 0 < σ) (paid : Draw Z σ C)
    (P : Finset (Bond c)) (X : Coat T F) (x : Site f) (ρ u : ℝ) (r j : ℕ)
    {y : E} {z : E → Arguments G c f} {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    Brush j (charge Z σ C ρ u j r t) 1 (fun w => ρ *
      (springPacketsAt Z u x (field P X (z w)) - sheet Z u P X (r+2) x (z w))) y := by
  induction Z with
  | nil =>
    simpa [charge, springPacketsAt, sheet] using
      (Brush.certified (k:=j) (x:=y) zero_le_one (0:ℝ))
  | cons a Z ih =>
    have h := paid.2 a List.mem_cons_self
    let W : book G (a.rise+2) := ⟨a.cells,σ,C,width,h.toll,h.hue⟩
    have ha := WilsonVacuumPreResetJointSite.measured W P X x r j
      (ρ*u^(a.grade-a.rise)) ht ht' read
    have hz := ih ⟨paid.1,fun b hb => paid.2 b (List.mem_cons_of_mem _ hb)⟩
    have both := ha.gathering hz
    apply both.shimmy (Filter.Eventually.of_forall fun w => ?_)
    have hp : printed W P X (r+2) x (z w) = entry a.cells P X (r+2) x (z w) := rfl
    simp only [hp, show W.words = a.cells from rfl, sheet, springPacketsAt,
      List.map_cons, List.sum_cons]
    ring

theorem funded (Z : SeriesA G) {σ C : ℝ} (width : 0 < σ) (paid : Draw Z σ C)
    (P : Finset (Bond c)) (X : Coat T F) (I : Finset (Site f)) (ρ u : ℝ) (r j : ℕ)
    {y : E} {z : E → Arguments G c f} {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    Brush j (I.card * charge Z σ C ρ u j r t) 1 (fun w => ∑ x ∈ I, ρ *
      (springPacketsAt Z u x (field P X (z w)) - sheet Z u P X (r+2) x (z w))) y := by
  simpa [nsmul_eq_mul] using Brush.spree I _ (fun _ => charge Z σ C ρ u j r t)
    zero_le_one (fun x _ => measured Z width paid P X x ρ u r j ht ht' read)

end YM.Integration.WilsonVacuumPreResetJointStack
