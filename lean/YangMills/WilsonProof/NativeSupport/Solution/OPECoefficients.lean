import YangMills.WilsonProof.NativeSupport.YangMills.OPECoefficientLaws
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YM.OPE.Orbits.Inclusions
import YM.OPE.Orbits.Clearance

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits
open Function Filter
open scoped BigOperators Classical Topology
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private theorem coordinateOfSingle (a : S.Tag) (w : ℕ) (c : Q.channels w) :
    (hierarchy F Q).singletonCoordinate a w c =
      (Q.basis w).coord c ((Q.stratum w).subtype.leftInverse
        (Q.cutTest w a.1 a.2)) := by
  let u : Q.stratum w := ⟨Q.fresh w (sole 0) 0 (sole a.2 : Labels S fun _ : Unit => a.1),
    Q.fresh_mem w (sole 0) 0 (sole a.2 : Labels S fun _ : Unit => a.1)⟩
  change (Q.basis w).coord c u = _
  have hu : (Q.stratum w).subtype u = Q.cutTest w a.1 a.2 := Q.single w a.1 a.2
  rw [← hu, LinearMap.leftInverse_apply_of_inj (Q.stratum w).ker_subtype]

theorem publicCoefficientLaws : (hierarchy F Q).CoefficientLaws := by
  constructor
  · intro I _ d w c x o
    let read := (Q.basis w).coord c ∘ₗ (Q.stratum w).subtype.leftInverse
    refine ⟨read.compMultilinearMap (Q.fresh w x o), fun v => ?_⟩
    let u : Q.stratum w := ⟨Q.fresh w x o v, Q.fresh_mem w x o v⟩
    change (Q.basis w).coord c u = (Q.basis w).coord c ((Q.stratum w).subtype.leftInverse
      ((Q.stratum w).subtype u))
    rw [LinearMap.leftInverse_apply_of_inj (Q.stratum w).ker_subtype]
  · intro I J _ _ e a b x o shift same w c
    change I → S.Tag at a
    change J → S.Tag at b
    let cap (j : J) := max (b j).1 (a (e j)).1
    let left (j : J) := F.sector.derivatives.rise (show (b j).1 ≤ cap j from le_max_left ..) (b j).2
    let right (j : J) := F.sector.derivatives.rise (show (a (e j)).1 ≤ cap j from le_max_right ..) (a (e j)).2
    have eq : left = right := by
      funext j
      apply S.pin_inj
      exact (F.sector.derivatives.stays Q.continuum.laws.toSymmetric Q.lifts _ _).trans
        ((same j).trans (F.sector.derivatives.stays Q.continuum.laws.toSymmetric Q.lifts _ _).symm)
    apply congrArg (fun u : Q.stratum w => (Q.basis w).repr u c)
    apply Subtype.ext
    change Q.fresh w (fun j => x (e j) + shift) (o + shift) (fun j => (b j).2) =
      Q.fresh w x o (fun i => (a i).2)
    refine (Q.fresh_transport w (x ∘ e) o (fun j => (b j).2) shift).trans ?_
    refine Eq.trans ?_ (Q.fresh_perm w x o (fun i => (a i).2) e)
    exact (Q.fresh_inclusions (h := cap) (fun j => le_max_left ..) (x ∘ e) o w _).symm.trans
      ((congrArg (Q.fresh w (x ∘ e) o) eq).trans
        (Q.fresh_inclusions (h := cap) (fun j => le_max_right ..) (x ∘ e) o w _))
  · intro w i j
    change Q.channels w at i j
    rw [coordinateOfSingle]
    change (Q.basis w).coord j ((Q.stratum w).subtype.leftInverse (Q.cutTest w w (Q.basis w i).val)) = _
    rw [Q.test_fixes _ _ (Q.basis w i).property]
    erw [LinearMap.leftInverse_apply_of_inj (Q.stratum w).ker_subtype (Q.basis w i)]
    classical
    by_cases same : i = j
    · subst j
      simp [Module.Basis.coord_apply, Module.Basis.repr_self]
    · simp [Module.Basis.coord_apply, Module.Basis.repr_self, Ne.symm same]
      exact same
  · intro d w different i j
    rw [coordinateOfSingle]
    change (Q.basis w).coord j ((Q.stratum w).subtype.leftInverse (Q.cutTest w d (Q.basis d i).val)) = 0
    rw [Q.test_orthogonal w d _ (Q.basis d i).property different, map_zero, map_zero]
  · intro h v
    have single := Q.packet_single h h le_rfl v
    rw [F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts] at single
    have sum := congrArg (S.pin h) single
    unfold Reader.packet at sum
    rw [map_sum] at sum
    refine Eq.trans (Finset.sum_congr rfl fun d _ => ?_) sum
    rw [F.sector.derivatives.stays Q.continuum.laws.toSymmetric Q.lifts,
      ← Q.assemble d.val (sole 0) (sole v : Labels S fun _ : Unit => h) 0, map_sum]
    exact Finset.sum_congr rfl fun c _ => ((S.pin d.val).map_smul _ _).symm
  · intro I A _ f a x o shrinks distinct w c
    filter_upwards [eventually_dock Q.port shrinks distinct w] with t margin
    let labels := stages (sole (S.unit 4) : Labels S fun _ : Unit => 4) (fun i => (a i).2)
    let caps := Sum.elim (fun _ : Unit => 4) (fun i => (a i).1)
    have present : Sum.elim (fun _ : Unit => (⟨4, (hierarchy F Q).unitAtFour⟩ : (hierarchy F Q).Tag)) a =
        fun i => ⟨caps i, labels i⟩ := by
      funext i
      cases i <;> rfl
    rw [present]
    apply congrArg (fun u : Q.stratum w => (Q.basis w).repr u c)
    apply Subtype.ext
    let z := x t (.inl ())
    let y := x t ∘ Sum.inr
    have split : x t = beside (sole z) y := by
      funext i
      rcases i with ⟨⟨⟩⟩ | i <;> rfl
    rw [split] at margin
    change Q.fresh w (x t) (o t) (stages (sole (S.unit 4) : Labels S fun _ : Unit => 4)
      (fun i => (a i).2)) = Q.fresh w y (o t) (fun i => (a i).2)
    rw [split]
    exact Q.fresh_unit y (o t) 4 (fun i => (a i).2) w z margin

end YangMills
