import YM.Integration.WilsonThermometerRegisteredPairRoom
import YM.Integration.WilsonThermometerAlignedCells

/-! The two independent microscopic displacements of the submitted compact three-point
profile fit the same original coarse capture halo, uniformly before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredAbsoluteRoom
open Lattice Wilson RG Extraction Cells RG12 Filter MeasureTheory Set XSpace Finset Source Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity FVA1 ActualRunUnmaskedPartners
open PhysicalNext.Repeat.Legato
open WilsonThermometerAlignedCells
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)

local notation "T" z:max => Site (R.family.side (z:UVIndex).1 z.2)
local notation "χ" r:max z:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
local notation "W₀" φ:max r:max z:max o:max => WilsonSeparatedOriginalThermometerCells.weight φ (χ r z) o

def mass (r:ℝ) (z:UVIndex) (φ:Test 3) (y:T z×T z):ℝ:=∑ c,‖W₀ φ r z (placedAt y c)‖

open private sum_triples from YM.Integration.WilsonThermometerAlignedCells

theorem costs (r:ℝ) (z:UVIndex) (φ:Test 3) (f:(T z)×(T z)→ℝ):
    ∑o:Fin 3→T z,‖W₀ φ r z o‖*f (offsets o)=∑y:T z×T z,mass R r z φ y*f y:=by
  rw [sum_triples];apply sum_congr rfl;intro y _
  rw [mass,sum_mul];apply sum_congr rfl;intro c _
  have off:offsets (placedAt y c)=y:=by cases y;simp [placedAt,offsets,atOrigin]
  rw [off]

theorem variation (r:ℝ) (z:UVIndex) (φ:Test 3) :
    ∑ y:T z×T z,mass R r z φ y≤∫x:Points 3,‖φ x‖:=by
  have all:=WilsonSeparatedOriginalThermometerCells.variation φ (χ r z)
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
  have collapse:=costs R r z φ (fun _=>1)
  simpa only [mul_one] using (le_of_eq (by simpa only [mul_one] using collapse.symm)).trans all

theorem active (r:ℝ) (z:UVIndex) (φ:Test 3) {y:T z×T z} (charged:mass R r z φ y≠0):
    ∃c:T z,∃x:Points 3,φ x≠0 ∧ (χ r z) x=placedAt y c:=by
  have live:∃c:T z,W₀ φ r z (placedAt y c)≠0:=by
    by_contra! zero
    apply charged;unfold mass;simp only [zero,norm_zero,sum_const_zero]
  obtain ⟨c,hc⟩:=live
  exact ⟨c,WilsonCapturedPrimaryCompactSites.active R φ r z (placedAt y c) hc⟩

theorem original_cell (r:ℝ) (z:UVIndex) (φ:Test 3) (o:Fin 3→T z)
    (charged:W₀ φ r z o≠0):mass R r z φ (offsets o)≠0:=by
  have placed:placedAt (offsets o) (o 0)=o:=by funext v;fin_cases v <;> simp [placedAt,offsets,atOrigin]
  have small:‖W₀ φ r z (placedAt (offsets o) (o 0))‖ ≤ mass R r z φ (offsets o):=
    Finset.single_le_sum (f:=fun c:T z=>‖W₀ φ r z (placedAt (offsets o) c)‖)
      (fun _ _=>norm_nonneg _) (mem_univ (o 0))
  rw [placed] at small
  exact ((norm_pos_iff.mpr charged).trans_le small).ne'

theorem spatial (simple:G.Simple) (φ:Test 3) : ∀ᶠ j:ℕ in atTop,
  ∀ (N per:ℕ) (live:j ≤ N) (r:ℝ), |r|≤R.family.S.a j → ∀y:Site (R.family.side N per) × Site (R.family.side N per),
  mass R r (N,per) φ y≠0 → ∀v:Fin 3,
  separation ((R.family.S.toDepth live per).parent (atOrigin y v)) 0 ≤ (R.family.path.levels.budget j).B:=by
  obtain ⟨K,shape⟩:=WilsonCapturedPrimaryCaptureRoom.shape φ
  have rise:=Multi.Wage.ranges simple R.family.path.levels
  filter_upwards [rise.eventually_ge_atTop (2*(K+1)+1)] with j large
  intro N per live r radius y tested
  obtain ⟨c,x,hx,location⟩:=active R r (N,per) φ tested
  let S:=R.family.S
  let g:=S.toDepth live per
  let z:=address (S.a N) (r • x)
  have fine:=S.a_pos N
  have coarse:=S.a_pos j
  have expand:S.a N*(g.count.val:ℝ)=S.a j:=S.embeds_scale g
  have count : (1:ℝ) ≤ (g.count.val:ℝ) := by exact_mod_cast g.count.property
  have mono:S.a N ≤ S.a j:=by rw [←expand];simpa only [mul_one] using mul_le_mul_of_nonneg_left count fine.le
  have fee (v:Fin 3) (a:Axis):|S.a N*(z v a:ℝ)|≤((K+1:ℕ):ℝ)*S.a j:=by
    have vertex:=(Extraction.tile_bounds fine ((r • x) v a) (z v a)).mp rfl
    change S.a N*((z v a:ℝ)-1)<r*x v a ∧ r*x v a≤S.a N*(z v a:ℝ) at vertex
    have mag:|S.a N*(z v a:ℝ)|≤|r*x v a|+S.a N:=by
      rw [abs_le]; exact ⟨by linarith [neg_abs_le (r*x v a),vertex.2],
        by linarith [le_abs_self (r*x v a),vertex.1]⟩
    rw [Nat.cast_succ,add_mul,one_mul]
    apply mag.trans (add_le_add _ mono)
    rw [abs_mul,mul_comm (K:ℝ)]
    exact mul_le_mul radius (shape x hx v a) (abs_nonneg _) coarse.le
  intro v
  have far:∀a, |S.a N*((z v-z 0) a:ℝ)|≤((2*(K+1):ℕ):ℝ)*S.a j:=by
    intro a
    change |S.a N*((z v a-z 0 a:ℤ):ℝ)|≤_
    rw [Int.cast_sub,mul_sub]
    calc
      _ ≤ |S.a N*(z v a:ℝ)|+|S.a N*(z 0 a:ℝ)| := abs_sub _ _
      _ ≤ ((K+1:ℕ):ℝ)*S.a j+((K+1:ℕ):ℝ)*S.a j := add_le_add (fee v a) (fee 0 a)
      _ = _ := by push_cast;ring
  have sockets (w:Fin 3): wrap (S.side N per) (z w)=atOrigin y w+c := congrFun location w
  have pos:atOrigin y v=wrap (S.side N per) (z v-z 0):=by
    rw [map_sub,sockets,sockets]
    change _=(_+c)-(0+c);abel
  rw [pos]
  exact (WilsonThermometerRegisteredPairRoom.integer S live _ _ far).trans large

end YM.Integration.WilsonThermometerRegisteredAbsoluteRoom
