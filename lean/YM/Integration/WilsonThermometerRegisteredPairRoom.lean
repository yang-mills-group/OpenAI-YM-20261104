import YM.Integration.WilsonThermometerRegisteredPairMass
import YM.Integration.WilsonCapturedPrimaryCaptureRoom

/-! At a true capture mesh the entire physical two-site stencil fits the original
halo uniformly in the fine cutoff and period, after translating the pivot to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredPairRoom
open Lattice Wilson RG Extraction Cells RG12 Filter MeasureTheory Set XSpace Finset Source Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity FVA1 ActualRunUnmaskedPartners
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)

theorem active (φ : Test 2) (r:ℝ) {i per:ℕ} (o:Site (R.family.side (i+2) per))
    (charged : WilsonThermometerRegisteredPairMass.mass R φ r o≠0) :
    ∃ x : Points 2,φ x ≠ 0 ∧ WilsonThermometerRegisteredPairMass.offset R (i:=i) (per:=per) r x = o := by
  classical
  by_contra bad
  let χ:=WilsonThermometerRegisteredPairMass.offset R (i:=i) (per:=per) r
  have vanish (x : Points 2) : (χ ⁻¹' {o}).indicator (fun u=>φ u) x=0 := by
    by_cases hx:χ x=o
    · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {o} from hx)]
      by_contra nonzero
      exact bad ⟨x,nonzero,hx⟩
    · exact Set.indicator_of_notMem (show x ∉ χ ⁻¹' {o} from hx) (fun u=>φ u)
  apply charged
  unfold WilsonThermometerRegisteredPairMass.mass WilsonThermometerRegisteredPairMass.weight
  change (∫ x:Points 2,(χ ⁻¹' {o}).indicator (fun u=>φ u) x)=0
  simp_rw [vanish]
  exact integral_zero _ _

theorem zero {a b:Side} (g:Ratio a b) : g.parent 0=0:=by
  have embed:g.embed 0=0:=g.root.map_zero
  simpa only [embed] using g.embed_parent (0:Site a)

theorem integer (S:Schedule) {N per j:ℕ} (hi:j≤N) (z:Cover) (K:ℕ)
    (wallet:∀ a,|S.a N*(z a:ℝ)|≤(K:ℝ)*S.a j):
    separation ((S.toDepth hi per).parent (wrap (S.side N per) z)) 0 ≤ K+1 :=by
  let g:=S.toDepth hi per
  let u:=wrap (S.side N per) z
  have fine:=S.a_pos N
  have coarse:=S.a_pos j
  have expand:S.a N*(g.count.val:ℝ)=S.a j:=S.embeds_scale g
  have distance : separation u 0 ≤ K*g.count.val := by
    rw [separation,sub_zero]
    apply Finset.sup_le
    intro a _
    apply (Corona.lap z a).trans
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_mul]
    have paid : S.a N*((z a).natAbs:ℝ) ≤ S.a N*((K:ℝ)*g.count.val) := by
      calc
        _ = |S.a N*(z a:ℝ)| := by
          rw [abs_mul,abs_of_pos fine]
          congr 1
          rw [← show (((↑(z a).natAbs:ℤ):ℝ))=_ from Int.cast_natCast _,Int.natCast_natAbs,Int.cast_abs]
        _ ≤ K*S.a j := wallet a
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

theorem shape (φ : Test 2) :
    ∃ K:ℕ,∀ x:Points 2,φ x ≠ 0 → ∀ v a,|x v a| ≤ (K:ℝ) := by
  let f (x : Points 2) := ∑ v:Fin 2,∑ a:Axis, |x v a|
  have smooth : Continuous f := by dsimp only [f];fun_prop
  obtain ⟨B,supremum⟩:=φ.hasCompactSupport.exists_bound_of_continuousOn smooth.continuousOn
  refine ⟨⌈B⌉₊,?_⟩
  intro x hx v a
  have mem : x ∈ tsupport (fun x=>φ x) := subset_closure hx
  have positive (v:Fin 2) (a:Axis): 0 ≤ |x v a| := abs_nonneg _
  calc
    |x v a| ≤ ∑ b:Axis,|x v b| := single_le_sum (fun b _=>positive v b) (mem_univ a)
    _ ≤ f x := single_le_sum
      (f:=fun w:Fin 2=>∑b:Axis,|x w b|) (fun w _=>sum_nonneg (fun b _=>positive w b)) (mem_univ v)
    _ ≤ ‖f x‖ := le_abs_self _
    _ ≤ B := supremum x mem
    _ ≤ _ := Nat.le_ceil _


theorem spatial (simple:G.Simple) (φ:Test 2) : ∀ᶠ j:ℕ in atTop,
  ∀ (i per:ℕ) (live:j ≤ i+2) (r:ℝ), |r|≤R.family.S.a j → ∀y:Site (R.family.side (i+2) per),
  WilsonThermometerRegisteredPairMass.mass R φ r y≠0 →
  separation ((R.family.S.toDepth live per).parent y) 0 ≤ (R.family.path.levels.budget j).B:=by
  obtain ⟨K,shape⟩:=shape φ
  have rise:=Multi.Wage.ranges simple R.family.path.levels
  filter_upwards [rise.eventually_ge_atTop (2*(K+1)+1)] with j large
  intro i per live r radius y tested
  obtain ⟨x,hx,location⟩:=active R φ r y tested
  let S:=R.family.S
  let g:=S.toDepth live per
  let z:=address (S.a (i+2)) (r • x)
  have fine:=S.a_pos (i+2)
  have coarse:=S.a_pos j
  have expand:S.a (i+2)*(g.count.val:ℝ)=S.a j:=S.embeds_scale g
  have count : (1:ℝ) ≤ (g.count.val:ℝ) := by exact_mod_cast g.count.property
  have mono:S.a (i+2) ≤ S.a j:=by rw [←expand];simpa only [mul_one] using mul_le_mul_of_nonneg_left count fine.le
  have fee (v:Fin 2) (a:Axis):|S.a (i+2)*(z v a:ℝ)|≤((K+1:ℕ):ℝ)*S.a j:=by
    have vertex:=(Extraction.tile_bounds fine ((r • x) v a) (z v a)).mp rfl
    change S.a (i+2)*((z v a:ℝ)-1)<r*x v a ∧ r*x v a≤S.a (i+2)*(z v a:ℝ) at vertex
    have mag:|S.a (i+2)*(z v a:ℝ)|≤|r*x v a|+S.a (i+2):=by
      rw [abs_le]; exact ⟨by linarith [neg_abs_le (r*x v a),vertex.2],
        by linarith [le_abs_self (r*x v a),vertex.1]⟩
    rw [Nat.cast_succ,add_mul,one_mul]
    apply mag.trans (add_le_add _ mono)
    rw [abs_mul,mul_comm (K:ℝ)]
    exact mul_le_mul radius (shape x hx v a) (abs_nonneg _) coarse.le
  have far:∀a, |S.a (i+2)*((z 1-z 0) a:ℝ)|≤((2*(K+1):ℕ):ℝ)*S.a j:=by
    intro a
    change |S.a (i+2)*((z 1 a-z 0 a:ℤ):ℝ)|≤_
    rw [Int.cast_sub,mul_sub]
    calc
      _ ≤ |S.a (i+2)*(z 1 a:ℝ)|+|S.a (i+2)*(z 0 a:ℝ)| := abs_sub _ _
      _ ≤ ((K+1:ℕ):ℝ)*S.a j+((K+1:ℕ):ℝ)*S.a j := add_le_add (fee 1 a) (fee 0 a)
      _ = _ := by push_cast;ring
  have pos:y=wrap (S.side (i+2) per) (z 1-z 0):=by
    rw [←location,map_sub];rfl
  rw [pos]
  exact (integer S live _ _ far).trans large

end YM.Integration.WilsonThermometerRegisteredPairRoom
