import YM.Integration.WilsonMaxwellThermometerWardFiled
import YM.Integration.WilsonOffsetReportingProducts

/-! The finite pole read is additive on literal signed Wilson fields. Both
its constant value on the identity configuration and its first nonconstant
radial coefficient keep the same incoming transfer and the same spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardLinear
open Function Filter Set Finset MeasureTheory Lattice Labels Source Wilson PertExtension PertExtension.Orb
open PertExtension.Series Chart Series.Radial Series.Tested PhysicalNext.Repeat.Legato
open WilsonMaxwellThermometerWardPupil WilsonMaxwellThermometerWardFiled
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side}

theorem zeroField (a:ℝ): PreTest (fun _:Config G n=>a) :=
  ⟨fun _ _ _=>rfl,⟨continuous_const,contDiffAt_const⟩,continuous_const⟩

theorem plus {f h:Config G n→ℝ} (a:PreTest f) (b:PreTest h):PreTest (f+h):=
  ⟨fun u ok U=>by simp only [Pi.add_apply,a.gauge u ok U,b.gauge u ok U],
    ⟨a.curved.boundedness.add b.curved.boundedness,a.curved.germ.add b.curved.germ⟩,
    a.continuous.add b.continuous⟩

theorem minus {f h:Config G n→ℝ} (a:PreTest f) (b:PreTest h):PreTest (f-h):=
  ⟨fun u ok U=>by simp only [Pi.sub_apply,a.gauge u ok U,b.gauge u ok U],
    ⟨a.curved.boundedness.sub b.curved.boundedness,a.curved.germ.sub b.curved.germ⟩,
    a.continuous.sub b.continuous⟩

theorem finance (even:Even n.val) (g:ℝ) (q:ℕ) {K f h:Config G n→ℝ} (test:PreTest K)
    (hf:PreTest f) (hh:PreTest h):
    reading g q K (f+h)=reading g q K f+reading g q K h:=by
  let u:=f-fun _=>f 1
  let v:=h-fun _=>h 1
  have left:PreTest (u*K):=WilsonMaxwellThermometerWardCompanion.multiply (minus hf (zeroField _)) test
  have right:PreTest (v*K):=WilsonMaxwellThermometerWardCompanion.multiply (minus hh (zeroField _)) test
  have eq:((f+h)-(fun _=>(f+h) 1))*K=u*K+v*K:=by
    funext x
    change ((f x+h x)-(f 1+h 1))*K x=(f x-f 1)*K x+(h x-h 1)*K x
    ring
  unfold reading
  rw [eq,added even left right]
  simp only [Pi.add_apply]
  change (f 1+h 1)*_+g^2*(_+_)=f 1*_+g^2*diagonalWith (tray G) (restrictedO (u*K)) (2+q)+
    (h 1*_+g^2*diagonalWith (tray G) (restrictedO (v*K)) (2+q))
  ring

theorem placed {d:ℕ} {F:Frame G d} (C:SectionData F) (c:F.Coeff) (L:ℂ→L[ℝ]ℝ)
    (o:Site n) {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C):
    PreTest (fun U:Config G n=>L (C.places c o U)):=by
  rw [show (fun U:Config G n=>L (C.places c o U))=(fun _=>L (c 0))+selected C c L o (active (F:=F))
    from funext (literal C c L o sound)]
  exact plus (zeroField _) (WilsonMaxwellThermometerWardCoefficient.admitted C c L o sound pop _)

def cash (R:Run G) {d:ℕ} (N p:ℕ) (x:R.family.label d) : (R.family.labels.level d).Coeff :=
  ((R.family.S.a N:ℂ)^d)⁻¹ • (R.family.labels.level d).scaled (R.family.path.levels.clock.threshold N)⁻¹
    ((R.family.factory d N p).terminal.symm x)

theorem measured (R:Run G) {d:ℕ} (N p:ℕ) (x:R.family.label d) (o:Site (R.family.side N p)):
    R.family.O N p x o=(R.family.localSection d).places (cash R N p x) o:=by
  funext U
  unfold Family.O TransferData.cylinder initial cash SectionData.places SectionData.evaluate
  simp [map_smul]

theorem actual (R:Run G) {d:ℕ} (N p:ℕ) (x:R.family.label d) (L:ℂ→L[ℝ]ℝ) (o:Site (R.family.side N p)):
    PreTest (fun U=>L (R.family.O N p x o U)):=by
  rw [measured]
  exact placed (R.family.localSection d) _ L o (R.makes.sections d) (ActualRunGradedKernels.section_valuation R d)

end YM.Integration.WilsonMaxwellThermometerWardLinear
