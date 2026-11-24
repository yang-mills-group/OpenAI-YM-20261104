import YM.Integration.WilsonThermometerInversionScore

/-! The complete phase-tested ordinary face obtained from all Laurent
sockets of the actual cutoff fields. One auxiliary inversion denominator
normalizes the entire finite sum. A proper face uses its own index subtype. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionFaces
open Function Filter Finset MeasureTheory Lattice Wilson Gauge Precision
open PhysicalNext.Repeat.Legato PertExtension PertExtension.Orb PertExtension.Series
open PertExtension.Series.Tested WilsonThermometerDeclaredSeeds WilsonThermometerInversionSockets
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] (d:V→ℕ)
    {n:Side} (o:V→Site n) (g τ:ℝ) (v:(j:V)→R.family.label (d j))
    (t:V→T→ℂ) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "O" => WilsonThermometerInversionSockets.word R d univ
local notation "w" => WilsonThermometerInversionSockets.charge R d univ
local notation "E" => WilsonThermometerFrozenCopies.word R d g τ v t

def face (u:ℝ) (U:Config G n) : ℝ :=
  (∏j:V,(u^(d j+1))⁻¹)*L (∏j:V,∑a:Choice R d j,(E) (entry R d j a) u x (o j) U)
def series (h:ℕ) : ℝ := ∑b:(j:V)→Choice R d j,
  Orb.diag (restrictedO ((O) b o g τ v t x L)) ((w) b+h)

theorem placed (u:ℝ) (live:u≠0) (U:Config G n) :
    face R d o g τ v t x L u U = ∑b:(j:V)→Choice R d j,
      u⁻¹ ^ ((w) b) *((O) b o g τ v t x L) U := by
  unfold face
  rw [Fintype.prod_sum,map_sum,mul_sum]
  exact sum_congr rfl (fun b _=>WilsonThermometerInversionFiling.restored R d univ b o g τ v t x L u live U)

private theorem sum_ratio {B:Type} [Fintype B] {n:Side} (q : B → Wilson.Config G n → ℝ) (h:∀b,Continuous (q b))
    (c:B→ℝ) (u:ℝ) : preExpectation (∑ b,c b • q b) u=∑b,c b*preExpectation (q b) u := by
  let z:=fun y : OEdge n → G.El =>preDensity u (liftLinks y)
  have hc : Continuous z := by
    refine Real.continuous_exp.comp ((((energy_cont.comp ?_).div_const 2).neg).div_const (u^2))
    exact Orb.lift_cont G
  have hi (b:B) : Integrable (fun y=>(c b*q b (liftLinks y))*z y) (PertExtension.Chart.physical G (OEdge n)) :=
    Continuous.integrable_of_hasCompactSupport ((continuous_const.mul ((h b).comp (Orb.lift_cont G))).mul hc)
      (HasCompactSupport.of_compactSpace _)
  unfold preExpectation preNum
  simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
  rw [integral_finsetSum _ (fun b _=>hi b),Finset.sum_div]
  apply sum_congr rfl;intro b _
  simp_rw [mul_assoc,integral_const_mul,mul_div_assoc]
  rfl

theorem finite (ev:Even n.val) :
    Aspiration (fun u=>preExpectation (face R d o g τ v t x L u) u)
      (series R d o g τ v t x L) := by
  let f (b:(j:V)→Choice R d j) (u:ℝ) :=
    u⁻¹ ^ ((w) b)*preExpectation ((O) b o g τ v t x L) u
  let a (b:(j:V)→Choice R d j) (j:ℕ) :=
    Orb.diag (restrictedO ((O) b o g τ v t x L)) ((w) b+j)
  have H:=Aspiration.sum univ f a (fun b _=>WilsonThermometerInversionSockets.finite R d univ b o g τ v t x L ev)
  have ha : ∑b,a b=series R d o g τ v t x L := by funext j;simp only [series,Finset.sum_apply];rfl
  rw [ha] at H
  intro j
  obtain ⟨C,hC,h⟩:=H j
  refine ⟨C,hC,?_⟩
  filter_upwards [h,Tested.eventually_pos] with u hu pos
  have hf : face R d o g τ v t x L u=∑b,u⁻¹^((w) b) • (O) b o g τ v t x L := by
    funext U;rw [placed R d o g τ v t x L u pos.ne'];simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have fe := sum_ratio (fun b=>(O) b o g τ v t x L) (fun b=>(incoming R d univ b o g τ v t x L).1.continuous)
    (fun b=>u⁻¹^((w) b)) u
  simp only [Pi.sub_apply] at hu ⊢
  rw [hf,fe]
  simpa only [f,Finset.sum_apply] using hu

end YM.Integration.WilsonThermometerInversionFaces
