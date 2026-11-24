import YM.Integration.WilsonPositionProgramPublicStations

/-! The same pooled catalogue, weak station and signed determining inverse
appear in every physical four-corner sum, even with moving coefficients. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicFourFrame
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East PhysicalNext.Repeat.Legato
open RG17 FullVolume Climb Next.UVStress PhysMS Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot
open WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank
open WilsonPositionProgramPublicStations WilsonPositionProgramPublicGram
open WilsonPositionProgramPublicOriented WilsonPositionProgramPublicContrast
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
    {l : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
    {d D : ℕ} {I : Type*} [Fintype I] (basis:Module.Basis I ℂ ((Bel R.family.book).Field d))

def Receipt (B : Profiles R d) (C : ℝ) {r : ℝ} (hr : 0<r)
    (arms : Bool → (y:S.Field d) → Arm R.family S (l:Filter _) d y) : Prop :=
  let x(i:I):=homogeneous F J Z r d (basis i)
  ∃ L:(B.probes.index→ℂ) →L[ℂ] (Bel R.family.book).Field d,
    ‖L‖≤C ∧ (∀v,L (samples F J Z B r v)=v) ∧
    (∀v,‖v‖^2 ≤ C^2*square (samples F J Z B r v)) ∧
    (∀ᶠ z in (l:Filter _), Roster F J Z basis B hr (fun b i=>(arms b (x i)).source) L z) ∧
    ∀ (signed:Signed) (test:I→I→Test 2) (a b:ℕ×ℕ→I→ℂ) (K T:ℝ),
      (∀ᶠ z in (l:Filter _),charge (a z)≤K) → (∀ᶠ z in (l:Filter _),charge (b z)≤T) →
      Tendsto (fun z=>assay (a z) (b z)
        (table F signed (fun i b=>arms b (x i)) (fun i b=>arms b (x i)) test z))
        (l:Filter _) (𝓝 0)

def Paid (probes:Profiles R d) (C r : ℝ) (cap:d≤D) {s B : ℝ}
    (stock:Bank F l D s B) : Prop :=
  ∃ (k:ℕ) (fits:D≤k) (W:Vane R.family k) (T:Spin.change S d)
    (A:Pair F stock cap W fits T r) (hr:0<r),
    W.checked f H k ∧ W.wheel.r=r ∧ D≤W.k ∧
    (0<purchaseWidth W ∧ 20*R.family.S.a (purchaseWidth W)<R.family.S.a (purchaseWidth W-1) ∧
      R.family.S.a (purchaseWidth W-1)<r*LogV r/32) ∧
    Receipt F J Z basis probes C hr A.arm

theorem original {z : Arch R.family} (simple:G.Simple) (bliss:Bliss F l z H)
    (lead:Leading F J) (income:∀d,∀ᶠ r in trail,Frame.obedient F H (J r) d) (cap:d≤D) :
    ∃ (T:ℕ) (B:Profiles R d) (C:ℝ), 0<C ∧ ∀ᶠ r in trail,
      let s:=WilsonThermometerUnitFilingFourPoolShell.radius z T r
      (∃ stock:Bank F l D s (dock s^T), Paid F J Z basis (H:=H) B C r cap stock) ∧
      ∀ (s w : ℝ) (stock:Bank F l D s w), Paid F J Z basis (H:=H) B C r cap stock := by
  obtain ⟨T,dates⟩ := WilsonPositionProgramPublicStations.original F simple bliss D
  obtain ⟨B,C,hC,paid⟩ := WilsonPositionProgramPublicOriented.original F J Z basis lead income simple
  refine ⟨T,B,C,hC,?_⟩
  filter_upwards [dates,paid,self_mem_nhdsWithin] with r available panel hr
  have positive : 0<r := hr
  obtain ⟨L,fee,read,gram,approve⟩ := panel
  have issue (s w : ℝ) (stock : Bank F l D s w) : Paid F J Z basis (H:=H) B C r cap stock := by
    obtain ⟨k,hk,W,good,atR,live,width,funded⟩ := available.2 s w stock
    obtain ⟨T,⟨A⟩⟩ := funded d cap
    refine ⟨k,hk,W,T,A,positive,good,atR,live,width,L,fee,read,gram,?_,?_⟩
    · exact approve positive (l:Filter _) bliss.lies (fun b i=> A.arm b (homogeneous F J Z r d (basis i)))
    · intro signed test a b K T aa bb
      exact WilsonPositionProgramPublicContrast.original F signed _ _ test bliss.lies a b aa bb
  exact ⟨⟨available.1.choose,issue _ _ _⟩,issue⟩

end YM.Integration.WilsonPositionProgramPublicFourFrame
