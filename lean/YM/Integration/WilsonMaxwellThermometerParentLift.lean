import YM.Integration.WilsonReportCellProjection
import YM.Integration.WilsonMaxwellThermometerShiftedPanel

/-! A common bulk translation may use the genuine parents of the three separate
microscopic insertions. Each parent is lifted near its own physical position
before the finite program is evaluated, including across a periodic seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerParentLift
open Lattice Extraction FullVolume RG Integration
open scoped BigOperators Classical

theorem lift_parent {c f : Side} (g : Ratio c f) (u : Cover) :
    ∃ v : Cover, wrap c v=g.parent (wrap f u) ∧
      g.count.val • v=WilsonReportCellProjection.ancestor g u := by
  let h := g.parent (wrap f u)
  let a := WilsonReportCellProjection.ancestor g u
  let r := a - g.count.val • lift h
  have same : wrap f a=wrap f (g.count.val • lift h) := WilsonReportCellProjection.exact_site g u
  have zero : wrap f r=0 := by rw [show r=a-g.count.val • lift h from rfl,map_sub,same,sub_self]
  have divides (i : Axis) : (f.val:ℤ)∣r i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (congrFun zero i)
  choose w hw using divides
  let v : Cover := fun i=>lift h i+(c.val:ℤ)*w i
  refine ⟨v,?_,?_⟩
  · have casted : wrap c v=wrap c (lift h) := by
      funext i
      change ((lift h i + (c.val:ℤ)*w i : ℤ) : ZMod c.val) = ((lift h i:ℤ):ZMod c.val)
      rw [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,add_zero]
    exact casted.trans (wrap_lift _)
  · funext i
    have q := hw i
    change a i-(g.count.val:ℤ)*lift h i = (f.val:ℤ)*w i at q
    rw [g.exact_size,Nat.cast_mul] at q
    change (g.count.val:ℤ)*(lift h i+(c.val:ℤ)*w i) = a i
    linarith [mul_comm (c.val:ℤ) (g.count.val:ℤ)]

theorem parents (S : Schedule) {k N : ℕ} (h : k≤N) (per : ℕ) {r : ℝ} (hr : 0<r)
    (x : Points 3) :
    ∃ v : Fin 3 → Cover, wrap _ ∘ v=(S.toDepth h per).parent ∘ wrap _ ∘ address (S.a N) (r • x) ∧
      dist (tag (S.a k/r) v) x ≤ 24*(S.a k/r) := by
  let g := S.toDepth h per
  let u := address (S.a N) (r • x)
  choose v hs hv using fun i=>lift_parent g (u i)
  refine ⟨v,funext hs,?_⟩
  have scaled : tag (S.a k/r) v = r⁻¹ • tag (S.a N) (WilsonReportCellProjection.ancestor g ∘ u) := by
    apply Points.flatten.injective
    ext i
    have th := congrFun (hv i.1) i.2
    change (g.count.val:ℤ)*v i.1 i.2=WilsonReportCellProjection.ancestor g (u i.1) i.2 at th
    change S.a k/r*(v i.1 i.2:ℝ)=r⁻¹*(S.a N*(WilsonReportCellProjection.ancestor g (u i.1) i.2:ℝ))
    rw [← th, Int.cast_mul,Int.cast_natCast,←S.embeds_scale g]
    ring
  have first := Extraction.approximate (S.a_pos N) (r • x)
  have second := WilsonReportCellProjection.coordinates S h per u
  rw [←dist_eq_norm] at second
  have cheap := S.strictAnti.antitone h
  have close : dist (tag (S.a N) (WilsonReportCellProjection.ancestor g ∘ u)) (r • x) ≤ 24*S.a k :=
    (dist_triangle _ (tag (S.a N) u) _).trans (by norm_num at first second; linarith only [first,second,cheap])
  rw [scaled,dist_eq_norm,← inv_smul_smul₀ hr.ne' x,←smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), ← dist_eq_norm]
  calc r⁻¹*dist (tag (S.a N) (WilsonReportCellProjection.ancestor g ∘ u)) (r • x)
        ≤ r⁻¹*(24*S.a k) := mul_le_mul_of_nonneg_left close (inv_nonneg.mpr hr.le)
       _ = 24*(S.a k/r) := by ring

end YM.Integration.WilsonMaxwellThermometerParentLift
