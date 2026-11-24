import YM.Integration.WilsonThermometerUnitFilingFourPoolBill
import YM.Integration.WilsonThermometerUnitFilingFourPoolArms

/-! A finite family of actual Wilson insertions at independent measurement dates on one public frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicSlots
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams GapsContact.Stamps PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open scoped Classical Topology BigOperators

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
  {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
  {H : (Bel R.family.book).Hierarchy}

/-- One independently dated measurement. Its public label, ultraviolet coordinates and reflected card refer to the same arm. -/
structure Slot (l : Ultrafilter (ℕ×ℕ)) (d : ℕ) (v : S.Field d) (s B : ℝ) where
  j : ℕ
  m : ℕ
  owns : R.family.ref d ≤ j
  fore : m ≤ j
  breadth : s < B * R.family.S.a j
  front : R.family.S.a m < s*B
  arm : Arm R.family S (l:Filter _) d v
  calendar : ∀ i, Vane R.family i
  station : ℕ
  admissible : d ≤ station
  frame : Spin.change S d
  date : (calendar station).k = j
  wall : purchaseWidth (calendar station) = m
  actual (q) : arm.source q = (calendar station).wheel.atCut q
    ⟨d,Nat.lt_succ_of_le admissible⟩ (frame.symm v)
  numerical (N p) (live : j < N) : Next.UVStress.quota R.family d j N p (arm.source (N,p)) ≤
    R.family.S.a j^d * (B*GapsContact.Ascent.cost F d s v)
  reflected : ∀ᶠ q : ℕ×ℕ in f.fuse, Cards.PaidAt R.family.S q.1 q.2 m (R.family.beta q.1 q.2)
    (B*GapsContact.Ascent.cost F d s v) (R.family.O q.1 q.2 (arm.source q) 0)

theorem buy {D j m : ℕ} {s B : ℝ}
    (pool : WilsonThermometerUnitFilingFourPool.Receipt F l s j m D B)
    (d : ℕ) (fit : d ≤ D) (v : S.Field d) :
    ∃ L : Slot F l d v s B, L.j=j ∧ L.m=m := by
  let card := pool.budget d fit
  obtain ⟨V,i,cap,T,hj,hm,paid⟩ := WilsonThermometerUnitFilingFourPoolArms.sharp card
  obtain ⟨Y,joined,quota,wall⟩ := paid v
  exact ⟨⟨j,m,card.owns,pool.fore,pool.breadth,pool.front,Y,V,i,cap,T,hj,hm,joined,
    fun N p h => by simpa only [mul_assoc] using quota N p h,wall⟩,rfl,rfl⟩

variable {I : Type} [Fintype I] (d A : I → ℕ) (v : ∀ i, RG17.Free R.family (d i))
  (atDate : I → ℝ → ℝ)

local notation "target" i:max r:max => homogeneous F J Z (outer z (A i) (atDate i r)) (d i) (v i)
local notation "placed" T:max i:max r:max => radius z T (atDate i r)
local notation "salary" T:max i:max r:max => (dock (placed T i r)^T *
  GapsContact.Ascent.cost F (d i) (placed T i r) (target i r))

/-- Each cutoff coordinate is fixed before the sites. All reflected cards may subsequently
be read simultaneously in the ordered extraction. -/
theorem original (simple : G.Simple) (bliss : Bliss F l z H) (lead : Leading F J)
    (frame : ∀ k : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) k)
    (D : ℕ) (cap : ∀i, d i ≤ D) (dates : ∀i, Tendsto (atDate i) trail trail) :
    ∃ (T : ℕ) (K : I→ℝ), (∀ i, 0≤K i) ∧ ∀ᶠ r in trail,
      ∃ L : ∀i,Slot F l (d i) (target i r) (placed T i r) (dock (placed T i r)^T),
        (∀i, (salary T i r)*(wilson z (atDate i r))^(WilsonThermometerUnitFilingFourPoolBill.exponent T (A i) (d i))
          ≤ K i) ∧
        ∀ᶠ q : ℕ×ℕ in f.fuse,∀i, Cards.PaidAt R.family.S q.1 q.2 (L i).m
          (R.family.beta q.1 q.2) (salary T i r) (R.family.O q.1 q.2 ((L i).arm.source q) 0) := by
  obtain ⟨T,pools⟩ := WilsonThermometerUnitFilingFourPool.original F simple bliss D
  choose K nonneg earns using fun i => WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead frame T (A i) (d i) (v i)
  refine ⟨T,K,nonneg,?_⟩
  have booked := eventually_all.mpr fun i => (dates i).eventually ((smaller F simple bliss T).eventually pools)
  have income := eventually_all.mpr fun i => (dates i).eventually (earns i)
  filter_upwards [booked,income] with r hr bill
  choose j m ok using hr
  choose L _ _ using fun i => buy F (ok i) (d i) (cap i) (target i r)
  exact ⟨L,bill,eventually_all.mpr fun i => (L i).reflected⟩

end YM.Integration.WilsonMeasuredPublicSlots
