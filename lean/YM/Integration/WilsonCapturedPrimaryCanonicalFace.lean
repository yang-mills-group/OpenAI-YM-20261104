import YM.Integration.WilsonCapturedPrimaryCutoffOath
import YM.Integration.WilsonCenteredPositiveFiling

/-! The microscopic face, its exact engineering return and the original field reader.
The true finite source is the common top product, on its distinct submitted sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCanonicalFace
open Function Finset Lattice Wilson Labels Source Marker RG Push.Local RG16 RG16.Literal
open Extra.Histories Trace.Physical Trace.Physical.GermGraph FVA1 Cells Extraction Table Climb Trace
open Trace.Pilot Next.UVStress Next.Foundations PhysicalNext.Repeat.Legato
open MergeProof MergeProof.East MergeProof.Accent QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading WilsonCapturedPrimaryCutoffOath
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
 {N per b i : ℕ} (top : b<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "J" => Stock.census (Fin 3)
local notation "head" => offered R A simple top o
local notation "bank" ib:max => WilsonReceivedCloseHistory.history (N:=N) R disks head i ib
local notation "value" F:max => LocalComparison.actualPush R.family N per i F
local notation "W" s:max => word R A o s
local notation "B" => R.family.path.rep N per i
local notation "T" d:max => R.family.labels.level d

theorem engineering {d:ℕ} {n:Side} {F:Labels.Frame G d} {P:Rep G n} {y:Site n} {G₀:Hol G}
    (q:Coefficient F n) (w:ℂ) (order:d ≤ P.p.order) (power:d ≤ P.p.power)
    (form:q.Format y G₀ P) {κ v:ℝ} (paid:q.remBound y P κ v) :
    Germ.projection F G₀ P.p.threshold y (stretch w q) = w • Germ.projection F G₀ P.p.threshold y q := by
  let m(a:ℂ) := stretch a q
  have one : m 1=q := by simp only [m,stretch, one_smul]
  have hl : IsLinearMap ℂ (fun a:ℂ=>(m a).x) ∧ IsLinearMap ℂ (fun a:ℂ=>(m a).regular) :=
    ⟨⟨fun a b=>add_smul ..,fun a b=>smul_assoc ..⟩,⟨fun a b=>add_smul ..,fun a b=>smul_assoc ..⟩⟩
  have hp := Germ.linear_projection F G₀ (o:=y) m order power
    (fun a=>stretch_format a form) (fun a=>⟨_,_,stretch_rem a paid⟩) hl
  simpa only [smul_eq_mul,mul_one,one] using hp.map_smul w 1

theorem original (ib : i ≤ b) (ref : ∀v,R.family.ref (grade v) ≤ N)
    (funded : WilsonCenteredCaptureClock.first R simple ≤ N) (d : ℕ) (opened : Opened R.family d i per)
    (s : (J).Mode) {P:Rep G (R.family.side i per)} (same : P.p=(B).p) (quiet : ∀U,(B).eval U=P.eval U)
    (q : Coefficient (T d) (R.family.side i per)) (form:q.Format 0 R.family.params P) {κ a:ℝ}
    (paid:q.remBound 0 P κ a) (heard : ∀U,q.density 0 (R.family.localSection d) P U =
      ((value ((bank ib) fired)) U).part s) :
    readPage R.family N per d (W s) i (by omega) = ((R.family.S.a i:ℂ)^d) •
      (Germ.projection (T d) R.family.params P.p.threshold 0 q) ∧
    topReport R.family N per d R.makes i opened (by omega) (W s) =
      (fitting d N per i R.makes opened (by omega)).symm (((R.family.S.a i:ℂ)^d) •
        Germ.projection (T d) R.family.params P.p.threshold 0 q) := by
  let c := (R.family.S.a i:ℂ)^d
  let grades (_:Unit) (v:Fin 3) : ℕ := grade v
  let values (_:Unit) (v:Fin 3) : R.family.label (grade v) :=
    A.station.wheel.atCut (N,per) (index A (grade v)) (vector A (Finset.univ : Finset (Fin 3)) v)
  let sites (_:Unit) := o.origin
  let faces (_:Unit) := s.val
  have exactWord : WilsonCenteredProductBooking.source R grades values sites faces (fun _=>1) {()} = W s := by
    funext U
    simp [WilsonCenteredProductBooking.source,WilsonCenteredOriginalProduct.word,word,grades,values,sites,faces]
    rfl
  have bill := WilsonCenteredPositiveFiling.booked R simple grades values sites faces (fun _=>1) {()} d i
    (fun _ _ v=>ref v) opened.post (by omega) funded
  rw [exactWord] at bill
  obtain ⟨_,_,_,all⟩:=bill
  have posted U : credit R.family N per d (W s) i (by omega) U = (stretch c q).density 0 (R.family.localSection d) P U := by
    rw [credit_at R A simple top o ib ref d s U,stretch_density,heard]
  have issued:=WilsonCenteredCanonicalFiling.original R (W s) opened opened.post (by omega)
      (all i le_rfl (by omega) opened).1 same quiet (stretch c q) (stretch_format c form) (stretch_rem c paid) posted
  have dim:=dimensions d N per i R.makes opened.post (by omega)
  have order : d ≤ P.p.order := same ▸ dim.1
  have power : d ≤ P.p.power := same ▸ dim.2
  rwa [engineering q c order power form paid] at issued

end YM.Integration.WilsonCapturedPrimaryCanonicalFace
