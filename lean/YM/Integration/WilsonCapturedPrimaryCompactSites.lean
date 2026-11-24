import YM.Integration.WilsonSeparatedOriginalThermometerCells
import YM.Corona.Spend
import YM.Next.RANK.Coordinates

/-! A nonzero actual compact cell mass supplies all three real positions
at once. Their genuine physical ancestors fit the reporting halo at capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCompactSites
open Lattice Wilson RG Extraction Cells RG12 Filter MeasureTheory Set XSpace
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)

theorem active (φ : Test 3) (r : ℝ) (z : UVIndex) (o : Fin 3 → Site (R.family.side z.1 z.2))
    (charged : WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z) o ≠ 0) :
    ∃ x : Points 3,φ x ≠ 0 ∧ WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x = o := by
  classical
  by_contra bad
  let χ:=WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
  have vanish (x : Points 3) : (χ ⁻¹' {o}).indicator (fun u=>φ u) x=0 := by
    by_cases hx:χ x=o
    · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {o} from hx)]
      by_contra nonzero
      exact bad ⟨x,nonzero,hx⟩
    · exact Set.indicator_of_notMem (show x ∉ χ ⁻¹' {o} from hx) (fun u=>φ u)
  apply charged
  unfold WilsonSeparatedOriginalThermometerCells.weight
  change (∫ x:Points 3,(χ ⁻¹' {o}).indicator (fun u=>φ u) x)=0
  simp_rw [vanish]
  exact integral_zero _ _

theorem ancestor (S : Schedule) {N per j n : ℕ} (hi : j ≤ N) (x : Points n) (K : ℕ)
    (room : ∀ v a, |x v a| + S.a j ≤ (K:ℝ)*S.a j) (v : Fin n) :
    let g:=S.toDepth hi per
    separation (g.parent (wrap (S.side N per) (address (S.a N) x v))) 0 ≤ K+1 := by
  let g:=S.toDepth hi per
  let z:=address (S.a N) x v
  let u:=wrap (S.side N per) z
  have fine:=S.a_pos N
  have coarse:=S.a_pos j
  have expand:S.a N*(g.count.val:ℝ)=S.a j:=S.embeds_scale g
  have count : (1:ℝ) ≤ (g.count.val:ℝ) := by exact_mod_cast g.count.property
  have mono:S.a N ≤ S.a j := by rw [←expand];simpa only [mul_one] using mul_le_mul_of_nonneg_left count fine.le
  have distance : separation u 0 ≤ K*g.count.val := by
    rw [separation,sub_zero]
    apply Finset.sup_le
    intro a _
    apply (Corona.lap z a).trans
    have vertex := (Extraction.tile_bounds fine (x v a) (z a)).mp rfl
    change S.a N*((z a:ℝ)-1) < x v a ∧ x v a ≤ S.a N*(z a:ℝ) at vertex
    have magnitude : |S.a N*(z a:ℝ)| ≤ |x v a|+S.a N := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le (x v a),vertex.2],by linarith [le_abs_self (x v a),vertex.1]⟩
    have allowed := (magnitude.trans (add_le_add le_rfl mono)).trans (room v a)
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_mul]
    have paid : S.a N*((z a).natAbs:ℝ) ≤ S.a N*((K:ℝ)*g.count.val) := by
      calc
        _ = |S.a N*(z a:ℝ)| := by
          rw [abs_mul,abs_of_pos fine]
          congr 1
          rw [← show (((↑(z a).natAbs:ℤ):ℝ))=_ from Int.cast_natCast _,Int.natCast_natAbs,Int.cast_abs]
        _ ≤ K*S.a j := allowed
        _ = _ := by rw [←expand]; ring
    exact (mul_le_mul_iff_right₀ fine).mp paid
  have zero : g.parent 0=0 := by
    have embed:g.embed 0=0:=g.root.map_zero
    simpa only [embed] using g.embed_parent (0:Site (S.side j per))
  have last:=Corona.foreshorten g u 0
  rw [zero] at last
  change separation (g.parent u) 0 ≤ K+1
  have final : g.count.val*separation (g.parent u) 0 ≤ g.count.val*(K+1) := calc
    _ ≤ separation u 0+g.count.val := last
    _ ≤ K*g.count.val+g.count.val := Nat.add_le_add_right distance _
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left final g.count.property

theorem original (φ : Test 3) (r : ℝ) (z : UVIndex) {j : ℕ} (live : j ≤ z.1)
    (K : ℕ) (o : Fin 3→Site (R.family.side z.1 z.2))
    (room : ∀ x:Points 3, φ x ≠ 0 → ∀ v a, |(r • x) v a|+R.family.S.a j ≤ (K:ℝ)*R.family.S.a j)
    (mass : WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z) o ≠ 0) (v : Fin 3) :
    separation ((R.family.S.toDepth live z.2).parent (o v)) 0 ≤ K+1 := by
  obtain ⟨x,hx,same⟩:=active R φ r z o mass
  rw [← same]
  exact ancestor R.family.S live (r • x) K (room x hx) v

end YM.Integration.WilsonCapturedPrimaryCompactSites
