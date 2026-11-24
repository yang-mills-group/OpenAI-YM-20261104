import YM.Integration.WilsonPublicOutputHorizon
import YM.Integration.WilsonPublicOutputSmooth

/-! A grade-six component dual to the named chiral cubic. This functional vanishes
on every strict lower shelf and applies to the same measured smooth packet. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputCubic
open Function Table Spec RG17 OPE OPE.Orbits PhysMS Climb
open Maxwell XSpace XSpace.Photo XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score MS MS.Land MS.Menus MS.Theater MS.Local.Physical
open PhysicalNext.Repeat.Legato WilsonPositionHomogeneousFrame WilsonMSDictionaryVector
open scoped Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)

/-- The independent top is pure weight six. -/
theorem grade (W:Initialize G) (V:Normalize.Store G) (simple:G.Simple) :
    part 6 6 (Rose.toll G) ≠ 0 ∧
    ∀ k:ℕ, k<6 → part 6 k (Rose.toll G)=0 := by
  have fixed : en (le_refl 6) (part 6 6 (Rose.toll G)) = Rose.toll G := by
    simp only [Rose.toll,Tornado.Tbk,map_smul,part_same]
  refine ⟨fun bad => WilsonPublicOutputHorizon.cubic_ne_zero W V simple ?_,?_⟩
  · rw [←fixed,bad,map_zero]
  · intro k small
    simp only [Rose.toll,Tornado.Tbk,map_smul,part_other _ small.ne _ ,smul_zero]

theorem original (W:Initialize G) (simple:G.Simple) :
    ∃ L:RG17.Free R.family 6→L[ℂ]ℂ,
      L (WilsonPublicOutputHorizon.cubic (R:=R))=1 ∧
      (∀ (k:ℕ) (hk:k<6) (v:On.Grade G k),
        L ((Maxwell.Free.fields R.family.labels 6).symm (en hk.le v))=0) ∧
      ∀ (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
        (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
        (n:ℕ) (d:Fin n→ℕ) (v:(i:Fin n)→RG17.Free R.family (d i)) (ψ:Test n)
        (r u:ℝ) (q:ℕ) (money:ℝ),
        let pub:=homogeneous F J Z r
        let actual:=(pub 6).symm (RG17.basket Q 6 (d:=d) (fun i=>pub (d i) (v i)) r ψ)
        let predicted:=prediction R.family d 6 Z M ν v ψ q u
        ‖actual-predicted‖ ≤ money → ‖L actual-L predicted‖ ≤ ‖L‖*money := by
  let B := Daylight (Press.portDeck G) 6
  have nz := WilsonPublicOutputHorizon.cubic_ne_zero W Z.store simple
  obtain ⟨i,hi⟩ : ∃ i, B.coord i (Rose.toll G) ≠ 0 := by
    by_contra! bad
    apply nz
    apply B.repr.injective
    ext j
    simpa only [map_zero,Finsupp.zero_apply,Module.Basis.coord_apply] using bad j
  let q := B.coord i (Rose.toll G)
  let cap := (en (le_refl 6)).comp ((part 6 6).comp (Maxwell.Free.fields R.family.labels 6).toLinearMap)
  let L := q⁻¹ • ((B.coord i).comp cap).toContinuousLinearMap
  refine ⟨L,?_,?_,?_⟩
  · change q⁻¹ * B.coord i (en (le_refl 6) (part 6 6
      (Maxwell.Free.fields R.family.labels 6 (WilsonPublicOutputHorizon.cubic (R:=R)))))=1
    rw [WilsonPublicOutputHorizon.cubic, LinearEquiv.apply_symm_apply]
    simpa only [q,Rose.toll,Tornado.Tbk,map_smul,part_same] using inv_mul_cancel₀ hi
  · intro k hk v
    change q⁻¹ * B.coord i (en (le_refl 6) (part 6 6
      (Maxwell.Free.fields R.family.labels 6 ((Maxwell.Free.fields R.family.labels 6).symm (en hk.le v)))))=0
    rw [LinearEquiv.apply_symm_apply,part_other _ hk.ne' _,map_zero,map_zero,mul_zero]
  · intro Q M ν n d v ψ r u k money pub actual predicted bound
    rw [←map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))
end YM.Integration.WilsonPublicOutputCubic
