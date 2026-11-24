import YM.Integration.WilsonSeparatedOriginalThermometerCells
import YM.Extraction.Gaps
import YM.OPE.Samples.Layout

/-! Physical separation on the first successor of a genuinely occupied
cell of the signed thermometer test, uniformly before the ultraviolet cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerFineCells
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction
open PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalThermometerCells
open scoped Topology BigOperators Classical Pointwise ContDiff

theorem occupied {S:Type} [Fintype S] (φ:Test 3) (χ:Points 3→S) (o:S)
    (live:WilsonSeparatedOriginalThermometerCells.weight φ χ o ≠ 0) : ∃x∈tsupport φ,χ x=o := by
  by_contra! no
  apply live
  unfold WilsonSeparatedOriginalThermometerCells.weight
  have zero (x:Points 3) : (χ ⁻¹' {o}).indicator (fun y=>φ y) x=0 := by
    by_cases atSite:χ x=o
    · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {o} from atSite)]
      exact image_eq_zero_of_notMem_tsupport (fun hx=>no x hx atSite)
    · exact Set.indicator_of_notMem (show x∉χ ⁻¹' {o} from fun hx=>atSite hx) (fun y : Points 3=>φ y)
  simp only [funext zero,integral_zero]

theorem separated {n:ℕ} {K:Set (Points n)} (S:Schedule) (compact:IsCompact K) (clear:K⊆conf n) :
    ∃c:ℝ,0<c ∧ ∀ᶠ p:ℕ in atTop,∀N (r:ℝ), 0<r → r≤1 → ∀x∈K,∀i j:Fin n,i≠j →
      let o:=wrap (S.side N p) ∘ address (S.a N) (r • x)
      r*c-2*S.a N ≤ S.a N*separation (o i) (o j) := by
  obtain ⟨c,pos,ready⟩ := Gaps.someGrows S compact clear
  obtain ⟨p₀,raw⟩ := ready.exists
  refine ⟨c,pos,?_⟩
  have full : IsCompact ((Set.Icc (0:ℝ) 1) • K) := isCompact_Icc.smul_set compact
  filter_upwards [Gaps.expand_equivalent S full] with p unwrapped
  intro N r rp cap x hx i j off
  let y := r • x
  let grid := tag (S.a N) (address (S.a N) y)
  have spaced:Gaps.someFine S p (r*c-2*S.a N) grid := by
    intro i j off
    obtain ⟨a,ha⟩:=raw x hx i j off
    have lead:=ha (0:ℤ)
    have lag : c≤|x j a-x i a| := by simpa [Gaps.distances,Real.dist_eq] using lead
    have root : y∈(Set.Icc (0:ℝ) 1) • K := ⟨r,⟨rp.le,cap⟩,x,hx,rfl⟩
    have pricing:=unwrapped y root i j a
    have scale : r*c≤|y j a-y i a| := by
      calc r*c ≤ r*|x j a-x i a| := mul_le_mul_of_nonneg_left lag rp.le
           _ = _ := by change _=|r*x j a-r*x i a|; rw [←mul_sub,abs_mul,abs_of_pos rp]
    have within (l:Fin n) : |grid l a-y l a|≤ S.a N := coord_grid_bound (S.a_pos N) y l a
    have cut : dist (y j a-y i a) (grid j a-grid i a) ≤ 2*S.a N := by
      rw [Real.dist_eq]
      calc
        _ = |(grid i a-y i a)-(grid j a-y j a)| := by congr 1; ring
        _ ≤ |grid i a-y i a|+|grid j a-y j a| := abs_sub .. 
        _ ≤ _ := by linarith only [within i,within j]
    refine ⟨a,fun z=>?_⟩
    have whole:=pricing z
    have tri:=dist_triangle (y j a-y i a) (grid j a-grid i a) ((z:ℝ)*Extraction.length S p)
    change |y j a-y i a|≤dist (y j a-y i a) _ at whole
    change _≤dist (grid j a-grid i a) _
    linarith only [whole,tri,cut,scale]
  exact Gaps.gridSeparation S _ rfl spaced j i (Ne.symm off)

variable {G:Gauge} (R:Run G) (φ:Test 3)
local notation "sites" r:max N:max p:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,p)

theorem actual (legal:tsupport φ⊆conf 3) :
    ∃c:ℝ,0<c ∧ ∀ᶠ p:ℕ in atTop,∀ (N i:ℕ) (h:i≤N) (r:ℝ), 0 < r → r ≤ 1 →
      ∀ z:Fin 3→Site (R.family.side N p), WilsonSeparatedOriginalThermometerCells.weight φ (sites r N p) z≠0 →
      ∀ v w, v ≠ w → ∀ b:ℕ,R.family.S.a i*b+2*R.family.S.a N≤r*c →
         b ≤ separation ((R.family.S.toDepth h p).parent (z v)) ((R.family.S.toDepth h p).parent (z w)) := by
  obtain ⟨c,pos,all⟩:=separated R.family.S φ.hasCompactSupport legal
  refine ⟨c,pos,?_⟩
  filter_upwards [all] with p bounds
  intro N i h r rp cap z live v w off b bpaid
  obtain ⟨x,hx,atSite⟩:=occupied φ (sites r N p) z live
  have fine:=bounds N r rp cap x hx v w off
  change r*c-2*R.family.S.a N≤R.family.S.a N*separation ((sites r N p) x v) ((sites r N p) x w) at fine
  rw [atSite] at fine
  let F:=R.family.S.toDepth h p
  have scale:= R.family.S.embeds_scale F
  have funds : F.count.val*b ≤ separation (z v) (z w) := by
    suffices hi : ((F.count.val*b:ℕ):ℝ)≤(separation (z v) (z w):ℝ) by exact_mod_cast hi
    apply le_of_mul_le_mul_left _ (R.family.S.a_pos N)
    rw [Nat.cast_mul,←mul_assoc,scale]
    linarith only [fine,bpaid]
  have strict:=(OPE.Log.Trunk.Canvas.expands (C:=R.family) (z v) (z w) h).2
  change separation (z v) (z w)<F.count.val*separation (F.parent (z v)) (F.parent (z w))+F.count.val at strict
  by_contra! low
  have bound:=Nat.mul_le_mul_left F.count.val (Nat.succ_le_of_lt low)
  rw [Nat.mul_succ] at bound
  exact (not_le_of_gt strict) (bound.trans funds)

end YM.Integration.WilsonOriginalThermometerFineCells
end
