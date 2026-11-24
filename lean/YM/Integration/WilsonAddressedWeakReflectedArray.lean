import YM.Integration.WilsonAddressedWeakDetectorCourse

/-! A finite reflected array of the prepared displaced weak pair. The two
trajectories are chosen once and then copied literally, including their
complete mixed regular and compulsory parts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakReflectedArray
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Table Spec Extraction XSpace
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open WilsonThermometerReflectedTrajectory WilsonAddressedWeakPointCells
open WilsonAddressedWeakCalibration
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {k N p : ℕ}
local notation "L" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem radius (live : k ≤ N) (ρ : ℝ) (hr : 0 < ρ) (x : Points 2) (Q : ℕ)
    (i : Fin 2) (inside : ‖x i‖ + 16*(R.family.S.a k/ρ) ≤ (R.family.S.a k/ρ)*Q) :
    separation ((R.family.S.toDepth live p).parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i)) 0 ≤ Q := by
  let b := lifts R (p:=p) live ρ hr x
  let y := projected R (p:=p) live ρ hr x
  let a := R.family.S.a k/ρ
  have pos : 0 < a := div_pos (R.family.S.a_pos _) hr
  obtain ⟨same,near⟩ := actual R (p:=p) live ρ hr x
  rw [same,separation,sub_zero]
  apply Finset.sup_le
  intro j _
  apply (Corona.lap (b i) j).trans
  have distance : dist (y i) (x i) ≤ 16*a := (PiLp.dist_apply_le y x i).trans near
  have mass : ‖y i‖ ≤ a*Q := by
    have tri := dist_triangle (y i) (x i) 0
    rw [dist_zero_right,dist_zero_right] at tri
    change ‖x i‖+16*a ≤ a*Q at inside
    linarith only [tri,distance,inside]
  have entry : |y i j| = a * |(b i j:ℝ)| := by
    change |ρ⁻¹*(R.family.S.a k*(b i j:ℝ))| = a*|(b i j:ℝ)|
    rw [←abs_of_pos pos,←abs_mul]
    congr 1
    dsimp [a];ring
  have component : |(b i j:ℝ)| ≤ (Q:ℝ) := by
    apply (mul_le_mul_iff_right₀ pos).mp
    rw [←entry]
    exact ((show |y i j| ≤ ‖y i‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (y i) j)).trans mass
  have en : |b i j| ≤ (Q:ℤ) := by exact_mod_cast component
  exact_mod_cast (show (((b i j).natAbs:ℤ)) ≤ (Q:ℤ) by simpa only [Int.natCast_natAbs] using en)

theorem shifted (live : k ≤ N) (z : Site (R.family.side N p)) (s : Motion) (c : Site (R.family.side k p)) :
    separation (WilsonThermometerReflectedTrajectory.point R z s c k) (anchorAt R c k) =
      separation ((R.family.S.toDepth live p).parent z) 0 := by
  let w := (R.family.S.toDepth live p).parent z
  let q := anchorAt R c k
  calc _ = separation (s.1.act w+q) (s.1.act (0:Site (R.family.side k p))+q) := by
         simp only [WilsonThermometerReflectedTrajectory.point,Lattice.affine,WilsonThermometerOwnOffsetNectar.location,
           dif_pos live,WilsonThermometerOwnOffsetTale.site];simp [w,q]
       _ = _ := by rw [separation_translate,separation_signed]

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) (D : ℕ) :
    ∃ (t u : ℕ), D+3 ≤ t ∧ D+3 ≤ u ∧ ∀ᶠ k : ℕ in atTop, ∀ p N (live : k ≤ N)
      (d : Fin 2 → ℕ) (_ : ∀ i,d i ≤ D) (ρ : ℝ) (_ : 0 < ρ) (x : Points 2) (Q : ℕ),
      (32+4*(((L).budget k).B^2:ℕ))*(R.family.S.a k/ρ) < dist (x 0) (x 1) →
      2*(dist (x 0) (x 1)+32*(R.family.S.a k/ρ)) < (R.family.side k p : ℝ)*(R.family.S.a k/ρ) →
      (∀ i, ‖x i‖+16*(R.family.S.a k/ρ) ≤ (R.family.S.a k/ρ)*Q) →
      let z := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
      ∃ (V : (i:Fin 2) → Sight R.family (d i) p) (r : (i:Fin 2) → Emblems R.family (d i)),
        (∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀ (Y : (i:Fin 2) → Palette R.family (d i)),
          let v := fun i => WilsonAddressedWeakNormalization.unit R (Y i)
          WilsonThermometerIntrinsicRoster.filed R d z v V r (Stock.census (Fin 2)) live t ∧
          ∀ (J:Type) [Fintype J] [DecidableEq J] (s:J→Motion) (c:J→Site (R.family.side k p)),
            (∀ j l, j ≠ l → ((L).budget k).B^2+2*Q < separation (anchorAt R (c j) k) (anchorAt R (c l) k)) →
            ∀ names : Census (J × Fin 2),
            WilsonThermometerReflectedRoster.filed R (fun i : J × Fin 2 => d i.2) (fun i=>z i.2) (fun i=>s i.1)
              (fun i=>c i.1) (fun i : J × Fin 2 => v i.2) (fun i=>V i.2) (fun i=>r i.2) names live u := by
  obtain ⟨t,w,dt,_,base⟩ := WilsonAddressedWeakDetectorCourse.original R simple shop D
  obtain ⟨u,du,many⟩ := WilsonThermometerReflectedRoster.original R simple shop D
  refine ⟨t,u,dt,du,?_⟩
  filter_upwards [base,many] with k get posts
  intro p N live d hd ρ hr x Q apart inside roots
  let z := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  obtain ⟨V,r,H,one⟩ := get p N live d hd ρ hr x apart inside
  refine ⟨V,r,H,?_⟩
  intro Y
  let v := fun i=>WilsonAddressedWeakNormalization.unit R (Y i)
  refine ⟨(one Y).1,?_⟩
  intro J _ _ s c clear names
  have cap (i : Fin 2) := WilsonAddressedWeakNormalization.allowed R (Y i)
  apply posts p N live (J × Fin 2) (fun i : J × Fin 2 => d i.2) (fun i=>hd i.2) (fun i=>z i.2)
    (fun i=>V i.2) (fun i=>r i.2) (fun i=>H i.2) (fun i=>s i.1) (fun i=>c i.1) _ names (fun i : J × Fin 2 => v i.2) (fun i=>cap i.2)
  rintro ⟨j,i⟩ ⟨l,h⟩ different
  by_cases same : j=l
  · subst l
    have ih : i ≠ h := fun eq=>different (Prod.ext rfl eq)
    rw [WilsonAddressedWeakDetectorCourse.translated R live]
    have sep := WilsonAddressedWeakSeparation.original R (p:=p) live ρ hr x (((L).budget k).B^2) apart inside
    fin_cases i <;> fin_cases h
    · exact (ih rfl).elim
    · exact sep
    · rw [separation_comm];exact sep
    · exact (ih rfl).elim
  · let q := anchorAt R (c j) k
    let q' := anchorAt R (c l) k
    let u' := WilsonThermometerReflectedTrajectory.point R (z i) (s j) (c j) k
    let v' := WilsonThermometerReflectedTrajectory.point R (z h) (s l) (c l) k
    have left : separation q u' ≤ Q := by rw [separation_comm,shifted R live];exact radius R live ρ hr x Q i (roots i)
    have right : separation v' q' ≤ Q := by rw [shifted R live];exact radius R live ρ hr x Q h (roots h)
    have near := separation_triangle q u' q'
    have far := separation_triangle u' v' q'
    have all : ((L).budget k).B^2+2*Q < separation q q' := clear j l same
    change _ < separation u' v'
    omega

end YM.Integration.WilsonAddressedWeakReflectedArray
