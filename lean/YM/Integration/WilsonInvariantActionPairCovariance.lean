import YM.Integration.WilsonInvariantActionOnePoint

/-! The exact original trace calibration on a connected two-field row.
The subtraction uses the two actual vacuum readings at this scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPairCovariance
open Filter Function Set MeasureTheory Table Spec Climb Trace.Pilot Trace.Over TraceExtension PhysMS
open OPE OPE.Orbits Next.UVStress Spin
open scoped Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
 (F : Final C f S) (J : ℝ→tower S)

def slot (b : S.Field 4) (x : Points 2) : S.Field 4→ₗ[ℂ]ℂ :=
  (S.classMoment S (fun _=>4) x).toLinearMap (fun _=>b) 0

theorem placed (b y : S.Field 4) (x : Points 2) :
    slot b x y=S.classMoment S (fun _=>4) x (Fin.cons y (fun _=>b)) := by
  change S.classMoment S (fun _=>4) x (Function.update (fun _:Fin 2=>b) 0 y)=_
  congr 1
  funext i
  fin_cases i <;> simp

include F in
theorem unit (b : S.Field 4) {x : Points 2} (hx : x∈conf 2) :
    slot b x (S.unit 4)=expectation S 4 b := by
  rw [placed]
  change S.useAt S x (fun i=>⟨4,Fin.cons (α:=fun _:Fin 2=>S.Field 4) (S.unit 4) (fun _=>b) i⟩)=_
  have inserted : (fun i:Fin 2=> (⟨4,Fin.cons (α:=fun _:Fin 2=>S.Field 4) (S.unit 4) (fun _=>b) i⟩:S.Tag))=
      Fin.cons ⟨4,S.unit 4⟩ (fun _=>⟨4,b⟩) := by funext i;fin_cases i <;> rfl
  rw [inserted,S.at_unit F.room.kernel.laws hx,vev_coordinates F.room.kernel.translations]
  exact (onepoint S b).symm

def covariance (y b : S.Field 4) (x : Points 2) : ℂ := slot b x (centering S 4 y)

include F in
theorem connected (y b : S.Field 4) {x : Points 2} (hx : x∈conf 2) :
    covariance y b x=S.classMoment S (fun _=>4) x (Fin.cons y (fun _=>b))-
      expectation S 4 y * expectation S 4 b := by
  rw [covariance,value_center,map_sub,map_smul,unit F b hx,smul_eq_mul,placed]

def tested (y b : S.Field 4) (r : ℝ) (φ : Test 2) : ℂ :=
  φ.applyTo (fun x=>covariance y b (r•x))

theorem charged (simple : G.Simple) {P : ℝ→change S 4} {δ g : ℝ→ℝ}
    (same : ∀ᶠr in trail,J r 4=P r) (cal : TendC F P δ) (coupling : Coupling G g) :
    ∀ᶠr in trail,∀ (b:S.Field 4) (φ:Test 2),
      tested (J r 4 (stepField C)) b r φ=((r^4/(4*δ r):ℝ):ℂ)* tested (center F) b r φ := by
  obtain ⟨c,value⟩:=WilsonInvariantActionOnePoint.resolved F J simple same cal coupling
  filter_upwards [value] with r hr b φ
  have central : centering S 4 (J r 4 (stepField C)) =
      ((r^4/(4*δ r):ℝ):ℂ) • centering S 4 (center F) := by
    rw [hr,show (r^4/(4*δ r):ℝ) • (center F-c • S.unit 4)=
        ((r^4/(4*δ r):ℝ):ℂ) • (center F-c • S.unit 4) from Complex.coe_smul ..,
      map_smul,map_sub,map_smul,const_out F.room.kernel.laws,smul_zero,sub_zero]
  unfold tested covariance
  simp_rw [central,map_smul,smul_eq_mul]
  unfold Test.applyTo
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

end YM.Integration.WilsonInvariantActionPairCovariance
