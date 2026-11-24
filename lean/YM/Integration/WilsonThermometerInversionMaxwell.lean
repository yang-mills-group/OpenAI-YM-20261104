import YM.Integration.WilsonThermometerInversionHead

/-! Maxwell ground at the intrinsic (6,4,4) top station. The retained
curvature rank is bounded by half the source's actual engineering grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionMaxwell
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Gauge Precision
open PhysicalNext.Repeat.Legato PertExtension PertExtension.Chart PertExtension.Orb
open PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonThermometerInversionHead WilsonThermometerInversionSockets
open scoped ContDiff Topology Classical BigOperators

variable {G:Gauge} {D:ℕ}
private theorem lexical (F:Labels.Frame G D) (i:F.Index) : 2*(F.grades i).2≤D := by
  let v:=F.basis i
  have h:v.val≠0:=fun e=>(Module.Basis.ne_zero F.basis i) (Subtype.ext e)
  obtain ⟨l,hL⟩:v.val.support.Nonempty:=Finset.nonempty_iff_ne_empty.mpr (fun e=>h (MvPolynomial.support_eq_empty.mp e))
  have hc := (pure_grade _ v).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hL)
  have hgrade : Finsupp.weight bidegree l=F.grades i := hc
  apply le_trans _ (F.bound i)
  rw [←hgrade,weight_slot]
  unfold height
  rw [Finsupp.weight_apply]
  unfold Finsupp.sum
  simp only [Finset.mul_sum]
  exact sum_le_sum fun j _=>by
    change 2*l j≤l j*generation j
    rw [mul_comm 2]
    exact Nat.mul_le_mul_left _ (show 2≤generation j from Nat.le_add_left _ _)

variable (R:Run G) {V T:Type} (d:V→ℕ)

theorem twice (i:Entry R d) : 2*pole R d i ≤ d (root R d i) := by
  rcases i with j | ⟨j,h,m⟩
  · exact Nat.zero_le _
  · exact lexical (R.family.labels.level (d j)) h

theorem thermometer (j:Fin 3) (a:Choice R WilsonOriginalThermometerPalette.levels j) :
    pole R WilsonOriginalThermometerPalette.levels (entry R _ j a) ≤ if j=0 then 3 else 2 := by
  have h:=twice R WilsonOriginalThermometerPalette.levels (entry R _ j a)
  rw [site] at h
  have cap : WilsonOriginalThermometerPalette.levels j = if j=0 then 6 else 4 := by fin_cases j <;> decide
  rw [cap] at h
  split_ifs at h ⊢ <;> omega

variable (s:Finset V) (b:(j:V)→Choice R d j) {n:Side} (o:V→Site n) (g τ:ℝ)
  (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "O" => WilsonThermometerInversionSockets.word R d s b o g τ v t x L
local notation "w" => WilsonThermometerInversionSockets.charge R d s b
local notation "e" j:max => entry R d j (b j)

theorem ground (ev:Even n.val) :
    Orb.diag (restrictedO (O)) (w) =
      (∫ u,(L (∏j∈s,t j x*scalar R d g τ v (e j))*∏j∈s,selected R d (e j) (o j) u)*
        kernel fiscal u ∂tangent G (Cotree n)) /
      (∫ u,kernel fiscal u ∂tangent G (Cotree n)) := by
  obtain ⟨hp,ho⟩:=incoming R d s b o g τ v t x L
  rw [Orb.diag,Orb.leading_row (traySpec G) hp.curved ho ev]
  simp_rw [radial R d s b o g τ v t x L]

end YM.Integration.WilsonThermometerInversionMaxwell
