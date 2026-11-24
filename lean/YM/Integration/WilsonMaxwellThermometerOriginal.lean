import YM.Integration.WilsonMaxwellThermometerQuadratic
import YM.Integration.WilsonMaxwellThermometerCapWords
import YM.Integration.WilsonMaxwellThermometerOriginalChirality
import YM.Integration.WilsonMaxwellThermometerLower

/-! The grade-zero coefficient of the original separated, rotation-tested
position thermometer at the intrinsic caps (6,4,4). -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerOriginal
open Set Maxwell Maxwell.Free XSpace XSpace.Chiral XSpace.Normalize XSpace.Rose
open WilsonMaxwellThermometerFaces WilsonMaxwellThermometerProfile WilsonMaxwellThermometerHeard
open WilsonMaxwellThermometerChiralReading WilsonMaxwellThermometerSignedAxes
open WilsonMaxwellThermometerLower
open scoped BigOperators
variable {G : Gauge} {V : Normalize.Store G}

theorem polar_pair (g : G.Simple) (K : Pick V) (c d : Bool) (u : WickPol G)
    (hu : u∈shellSector G 6) : read K (polar G c) (polar G d) u=0 := by
  let W := (read K (polar G c) (polar G d)).ker
  apply WilsonMaxwellThermometerCapWords.covers g W _ _ _ hu
  · exact of_profile K _ _ _ fun x _ => (WilsonMaxwellThermometerSeven.units x _ _).2.2
  · intro j l h; apply Submodule.span_le.mpr
    rintro _ ⟨a,b,rfl⟩; exact WilsonMaxwellThermometerQuadratic.complete K c d h a b
  · exact WilsonMaxwellThermometerHeard.odd K c d

private def lower_read (K : Pick V) (u : WickPol G) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun p q => read K p q u)
    (fun p p' q => add_left K u p p' q)
    (fun c p q => smul_left K u p q c)
    (fun p q q' => add_right K u p q q')
    (fun c p q => smul_right K u p q c)

private theorem prices (g : G.Simple) (K : Pick V) (u : Sec G 6) (v w : WickPol G)
    (hv : v=1 ∨ ∃ c, v=polar G c) (hw : w=1 ∨ ∃ d, w=polar G d) :
    read K v w u.val=0 := by
  rcases hv with rfl|⟨c,rfl⟩
  · exact of_profile K u.val 1 w fun x _ => (WilsonMaxwellThermometerSeven.units x u.val w).1
  rcases hw with rfl|⟨d,rfl⟩
  · exact of_profile K u.val (polar G c) 1 fun x _ =>
      (WilsonMaxwellThermometerSeven.units x u.val (polar G c)).2.1
  exact polar_pair g K c d u.val u.property

private theorem inner (g : G.Simple) (K : Pick V) (u : Sec G 6) (v : WickPol G)
    (hv : v=1 ∨ ∃ c, v=polar G c) : palette G ≤ (lower_read K u.val v).ker := by
  apply Submodule.span_le.mpr
  intro w hw; change read K v w u.val=0
  exact prices g K u v w hv hw

theorem tested (g : G.Simple) (K : Pick V) (u : Sec G 6) (p q : Sec G 4)
    (fp : ∀ (c : P) (i j : Axis), reflectPol (frame c i j).ortho p.val=p.val)
    (fq : ∀ (c : P) (i j : Axis), reflectPol (frame c i j).ortho q.val=q.val) :
    read K p.val q.val u.val=0 := by
  have hp:=classified g p.val p.property fp
  have hq:=classified g q.val q.property fq
  have outer : palette G ≤ ((lower_read K u.val).flip q.val).ker := by
    apply Submodule.span_le.mpr
    intro v hv
    change ((lower_read K u.val).flip q.val) v=0
    rw [LinearMap.flip_apply]
    have e : q.val ∈ (lower_read K u.val v).ker := (inner g K u v hv) hq
    exact e
  have e : p.val ∈ ((lower_read K u.val).flip q.val).ker := outer hp
  exact e

theorem original (g : G.Simple) (K : Pick V) (u : Sec G 6) (p q : Sec G 4)
    (fp : ∀ (c : P) (i j : Axis), reflectPol (frame c i j).ortho p.val=p.val)
    (fq : ∀ (c : P) (i j : Axis), reflectPol (frame c i j).ortho q.val=q.val) :
    (Rose.test K).applyTo (fun x => connected x (Graph3.trip u
      (up (by decide : 4≤6) p) (up (by decide : 4≤6) q)))=0 := by
  simp_rw [← WilsonMaxwellThermometerProfile.original]
  exact tested g K u p q fp fq

/-- The actual corrected cap-four source used in each lower thermometer slot. -/
abbrev lower (G : Gauge) : Sec G 4 :=
  ((Rose.f:ℂ)^2) • en (le_refl 4) (Chiral.Ufield G)

private theorem source_fixed (G : Gauge) (c : P) (i j : Axis) :
    ori (frame c i j).ortho 4 (lower G)=lower G := by
  apply Subtype.ext
  change reflectPol _ (((Rose.f:ℂ)^2) • Chiral.U G)=((Rose.f:ℂ)^2) • Chiral.U G
  rw [WilsonMaxwellThermometerOriginalChirality.original]
  simp only [map_smul,preserved]

theorem moved (g : G.Simple) (K : Pick V) (u : Sec G 6) (T : Module.End ℂ (Sec G 4))
    (comm : ∀ (s : Signed) (p : Sec G 4), ori s.ortho 4 (T p)=T (ori s.ortho 4 p)) :
    (Rose.test K).applyTo (fun x => connected x (Graph3.trip u
      (up (by decide : 4≤6) (T (lower G))) (up (by decide : 4≤6) (T (lower G)))))=0 := by
  have fix (c : P) (i j : Axis) :
      ori (frame c i j).ortho 4 (T (lower G))=T (lower G) := by
    rw [comm, source_fixed]
  exact original g K u _ _ (fun c i j => congrArg Subtype.val (fix c i j))
    (fun c i j => congrArg Subtype.val (fix c i j))

end YM.Integration.WilsonMaxwellThermometerOriginal
