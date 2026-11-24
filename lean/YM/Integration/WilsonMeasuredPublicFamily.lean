import YM.Integration.WilsonMeasuredPublicBank
import YM.Integration.WilsonMeasuredPublicRough

/-! All separated public sources on one preframe, at their own measurement dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicFamily
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams GapsContact.Stamps PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open WilsonMeasuredPublicSlots WilsonMeasuredPublicBank WilsonMeasuredPublicRough
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy}
    {I A : Type} [Fintype I] [Fintype A] (date : A → ℝ → ℝ) (key : I → A)
    (d a : I → ℕ) (v : ∀i,RG17.Free R.family (d i)) (D:ℕ) (cap:∀i,d i≤D)
local notation "atDate" i:max r:max => date (key i) r
local notation "target" i:max r:max => homogeneous F J Z (outer z (a i) (atDate i r)) (d i) (v i)
local notation "height" T:max h:max r:max => radius z T (date h r)
local notation "amp" T:max h:max r:max => dock (height T h r)^T
local notation "wage" T:max i:max r:max => amp T (key i) r *
  Ascent.cost F (d i) (height T (key i) r) (target i r)
local notation "exponent" T:max i:max => WilsonThermometerUnitFilingFourPoolBill.exponent T (a i) (d i)

/-- Each grade at a common date is printed in one original chart, before the test,
the finite group configuration and the independent locations have been specified. -/
theorem original (simple : G.Simple) (bliss : Bliss F l z H) (lead : Leading F J)
    (frame : ∀ e : ℕ, ∀ᶠ r in trail,Frame.obedient F H (J r) e)
    (dates : ∀h,Tendsto (date h) trail trail) :
    ∃ (T:ℕ) (K:I→ℝ), (∀i,0≤K i) ∧ ∀ᶠ r in trail,
      ∃ stock : ∀h,Bank F l D (height T h r) (amp T h r),
      let L (i:I) := ((stock (key i)).department (d i) (cap i)).print (target i r)
      (∀i,(wage T i r)*(wilson z (atDate i r))^(exponent T i) ≤ K i) ∧
      (∀i N p,(stock (key i)).j<N →
        Next.UVStress.quota R.family (d i) (stock (key i)).j N p ((L i).arm.source (N,p)) *
          (wilson z (atDate i r))^(exponent T i) ≤ R.family.S.a (stock (key i)).j^(d i) * K i) ∧
      (∀ n (i:Fin n→I) (t:Test n),Tendsto (fun q:ℕ×ℕ=>Order.smears R.family q.1 q.2
        (fun j=>⟨d (i j),(L (i j)).arm.source q⟩) t) (l:Filter _)
        (𝓝 (t.applyTo (fun x=>S.classMoment S (fun j=>d (i j)) x (fun j=>target (i j) r))))) ∧
      ∀ᶠ q:ℕ×ℕ in f.fuse,∀ keep:Finset I,Offers (fun i:keep=>L i.1) q := by
  obtain ⟨T,pools⟩ := before F l simple bliss D
  choose K hK earned using fun i=>WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead frame T (a i) (d i) (v i)
  have positive := (wilson_link F simple bliss.budgets bliss.keen bliss.lies).positive
  have germ := eventually_all.mpr fun i=>(dates (key i)).eventually (earned i)
  have sign := eventually_all.mpr fun i=>(dates (key i)).eventually positive
  refine ⟨T,K,hK,?_⟩
  filter_upwards [pools A date dates,germ,sign] with r booked cash hp
  let stock := booked.some
  let L (i:I) := ((stock (key i)).department (d i) (cap i)).print (target i r)
  refine ⟨stock,cash,?_,?_,?_⟩
  · intro i N p live
    have hj := (((stock (key i)).department (d i) (cap i)).dated (target i r)).1
    have hnum := (L i).numerical N p (hj.symm ▸ live)
    rw [hj] at hnum
    apply (mul_le_mul_of_nonneg_right hnum (pow_nonneg (hp i).le _)).trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (cash i) (pow_nonneg (R.family.S.a_pos _).le _)
  · intro n i t
    exact WilsonMeasuredPublicCopies.smooth bliss.lies (fun j=>L (i j)) t
  · exact eventually_all.mpr fun (keep:Finset I) => WilsonMeasuredPublicRough.original (fun i:keep=>L i.1)

end YM.Integration.WilsonMeasuredPublicFamily
