import YM.Integration.WilsonPositionGradedThermometerHearing
import YM.Integration.WilsonMaxwellThermometerOriginal

/-! The constant Maxwell coefficient of the seven actual signed station fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionGradedThermometerGround
open Function Set Filter Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {C : Family G}
variable {f : Extraction.Order} {S : Table R.family.book} {Y : Ultrafilter (ℕ × ℕ)}
variable {H : (Bel R.family.book).Hierarchy} {V : Store G}

def transform (A : Group C 6) (j : Fin 7) : Module.End ℂ (Sec G j) :=
  let b := Maxwell.Free.fields C.labels j
  ((b.symm.trans (A.change j)).trans b).toLinearMap

def tags (A : Group C 6) : XSpace.Structure1.Tags G 6 3 :=
  XSpace.Graph3.trip (transform A 6 (Rose.toll G))
    (up (by decide : 4≤6) (transform A 4 (lower G)))
    (up (by decide : 4≤6) (transform A 4 (lower G)))

def ground (A : Group R.family 6) (x : Points 3) : ℂ :=
  WilsonPositionThermometerConnected.value (fun s=>
    WickGoal (C:=R.family) (d:=fun i=>(grade i).val) (WilsonPositionThermometerGradedReading.vector A s) x)

private theorem moved (A : Group C 6) (j : Fin 7) (spin : (Bel C.book).RealSpin)
    (coherent : Coherent spin spin j (A.change j)) (s : Signed) (p : Sec G j) :
    ori s.ortho j (transform A j p)=transform A j (ori s.ortho j p) := by
  let b := Maxwell.Free.fields C.labels j
  have axis (x : (Bel C.book).Field j) : b ((Bel C.book).mirror spin j s x) = ori s.ortho j (b x) :=
    Subtype.ext (Maxwell.Free.address_motion C.labels s x)
  have inner : b.symm (ori s.ortho j p)=(Bel C.book).mirror spin j s (b.symm p) := by
    apply b.injective
    rw [LinearEquiv.apply_symm_apply,axis,LinearEquiv.apply_symm_apply]
  change ori s.ortho j (b (A.change j (b.symm p)))=b (A.change j (b.symm (ori s.ortho j p)))
  rw [inner,coherent.signed,axis]

theorem faces (A : Group R.family 6)
    (unit : ∀ j : Fin 7, A.change j ((Bel R.family.book).unit j) = (Bel R.family.book).unit j)
    (x : Points 3) (s : Rose.Badge) :
    WickGoal (C:=R.family) (d:=fun i=>(grade i).val) (WilsonPositionThermometerGradedReading.vector A s) x =
      WilsonMaxwellThermometerFaces.faces x (tags A) s := by
  let a : Fin 3 → (Bel R.family.book).Tag := fun i=>⟨(grade i).val, WilsonPositionThermometerGradedReading.vector A s i⟩
  change (Bel R.family.book).useAt (Bel R.family.book) x a = _
  rw [Maxwell.Free.display]
  have columns : Maxwell.Free.supply R.family.labels ∘ a = fun i=>(Rose.missing (tags A) s i).val := by
    funext i
    change Maxwell.Free.address R.family.labels _ (WilsonPositionThermometerGradedReading.vector A s i) = _
    by_cases hi : i∈s
    · rw [Maxwell.Free.address_eval]
      simp only [WilsonPositionThermometerGradedReading.vector,source,hi,if_true,Rose.missing]
      fin_cases i <;> rfl
    · rw [WilsonPositionThermometerGradedReading.vector,WilsonPositionThermometerGradedSource.unit _ _ _ hi,
          unit,Maxwell.Free.unit_address]
      simp only [Rose.missing,hi,if_false]; rfl
  rw [columns]
  rfl

theorem tested (simple : G.Simple) (K : Rose.Pick V) (A : Group R.family 6)
    (coherent : Coherent H.spin H.spin 4 (A.change 4))
    (unit : ∀ j : Fin 7, A.change j ((Bel R.family.book).unit j) = (Bel R.family.book).unit j) :
    (Rose.test K).applyTo (ground A) = 0 := by
  have same : ground A = fun x=>WilsonMaxwellThermometerFaces.connected x (tags A) := by
    funext x
    unfold ground
    simp_rw [faces A unit]
    simp only [WilsonPositionThermometerConnected.value,WilsonMaxwellThermometerFaces.connected,Rose.b3,
      two_smul,map_add,map_sub,map_mul,PowerSeries.constantCoeff_C]
    ring
  rw [same]
  exact WilsonMaxwellThermometerOriginal.moved simple K _ _ (moved A 4 H.spin coherent)

variable (F : Final R.family f S) (J : ℝ → tower S) (V : Store G) (K : Rose.Pick V)
    (A : ℝ → Group R.family 6) (book : Book (f:=f) (l:=Y) (H:=H) A J)
local notation "P" => WilsonPositionPrescribedFrame.positioned F J V

include book in
/-- The exact free coefficient and the signed interacting cutoff reading use the same transported
three fields, their actual units on proper faces, and the same real normalization test. -/
theorem original (lead : Leading F J) (simple : G.Simple) (prior : (Y : Filter _) ≤ f.fuse) :
    ∀ᶠ r in trail,
      (Rose.test K).applyTo (ground (WilsonPositionCorrectedCap.adjusted F J V A r)) = 0 ∧
      Tendsto (WilsonPositionGradedThermometerHearing.offer F J V K A r) (Y : Filter _)
        (𝓝 (WilsonPositionThermometerReading.tested F P K r)) := by
  filter_upwards [WilsonPositionCorrectedCap.original F J V A book lead 0,
    WilsonPositionGradedThermometerHearing.signed F J V lead K A book simple prior] with r proj cut
  exact ⟨tested (H:=H) simple K _ (proj.2.2.2.2.1 4).1 (fun j=>(proj.2.2.2.2.1 j).2.1),cut⟩

end YM.Integration.WilsonPositionGradedThermometerGround
