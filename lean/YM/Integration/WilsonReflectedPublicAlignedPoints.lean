import YM.Integration.WilsonReflectedEmbeddedLocations
import YM.Integration.WilsonThermometerUnitFilingFourSquare
import YM.OPE.Coverage.Passage

/-! The original moving cutoff representatives at independently chosen sites
of one reporting grid. Each insertion keeps its own integer grid position. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicAlignedPoints
open Filter Set Extraction Wilson Lattice RG PhysicalNext.Repeat.Legato Spec Table Next.UVStress
open WilsonThermometerUnitFilingFourSquare
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family

theorem grid {m N : ℕ} (mn : m ≤ N) (p : ℕ) {n : ℕ} (o : Fin n → Cover) (i : Fin n) :
    wrap ((C₀).side N p) (address ((C₀).S.a N) (tag ((C₀).S.a m) o) i) =
      ((C₀).S.toDepth mn p).embed (wrap ((C₀).side m p) (o i)) := by
  let g := (C₀).S.toDepth mn p
  have atFine : tag ((C₀).S.a m) o = tag ((C₀).S.a N) (fun j => g.count.val • o j) := by
    ext j a
    change (C₀).S.a m * (o j a : ℝ) = (C₀).S.a N * ((g.count.val • o j a : ℤ) : ℝ)
    rw [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,WilsonReflectedEmbeddedLocations.count R mn p]
    field_simp [((C₀).S.a_pos N).ne']
  rw [atFine,address_matched ((C₀).S.a_pos _),Ratio.embed_wrap]

variable {R} {S : Table R.family.book} {f : Extraction.Order} (F : Final R.family f S)
    {l : Filter (ℕ×ℕ)} [l.NeBot] {n : ℕ} {d : Caps n} {v : (i : Fin n) → S.Field (d i)}

include F

theorem measured (order : l ≤ f.fuse) (x : Points n) (gen : x ∈ generic n) (sep : x ∈ conf n)
    (A : ∀ i, Arm R.family S l (d i) (v i)) :
    Tendsto (fun z : ℕ×ℕ => R.family.ensemble d
      (fun i => wrap (R.family.side z.1 z.2) (address (R.family.S.a z.1) x i))
      (fun i => (A i).source z)) l (𝓝 (S.classMoment S d x v)) := by
  let M := fun z : ℕ×ℕ => R.family.ensemble d
    (fun i => wrap (R.family.side z.1 z.2) (address (R.family.S.a z.1) x i))
  let Y := fun i => (A i).label
  have fixed (z : R.family.book.Vector d) :
      Tendsto (fun u => M u z) l (𝓝 (S.value d x z)) :=
    OPE.Coverage.Pass.rounded R.family z f l order F.room.generic x gen
  have move := tendsto_multi (fun i => R.family.book.Ref (d i)) M (fun z => S.value d x z)
    fixed Y (fun z i => (A i).source z) (fun i => (A i).approaches)
  have eq := S.class_agrees S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) d sep Y
  have ids : (fun i => S.project (d i) (Y i)) = v := funext fun i => (A i).represents
  rw [ids] at eq
  exact eq.symm ▸ move

theorem aligned (order : l ≤ f.fuse) (m : ℕ) (o : Fin n → Cover)
    (gen : tag (R.family.S.a m) o ∈ generic n) (sep : tag (R.family.S.a m) o ∈ conf n)
    (A : ∀ i, Arm R.family S l (d i) (v i)) :
    Tendsto (fun z : ℕ×ℕ => R.family.ensemble d
      (fun i => if h : m ≤ z.1 then (R.family.S.toDepth h z.2).embed (wrap _ (o i)) else 0)
      (fun i => (A i).source z)) l (𝓝 (S.classMoment S d (tag (R.family.S.a m) o) v)) := by
  apply (measured F order _ gen sep A).congr'
  have after : ∀ᶠ z : ℕ×ℕ in f.fuse, m ≤ z.1 := by
    rw [Order.fused]
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop m
  filter_upwards [after.filter_mono order] with z hz
  simp only [dif_pos hz]
  simp_rw [grid R hz z.2 o]

end YM.Integration.WilsonReflectedPublicAlignedPoints
end
