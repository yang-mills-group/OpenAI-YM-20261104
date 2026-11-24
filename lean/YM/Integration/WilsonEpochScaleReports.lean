import YM.Integration.WilsonEpochScalePolynomials

/-! At fixed order, the exact lattice deposit and the original smeared MS
coefficient have the same uniform bound on their degree in log scale.
The lattice sum uses every authentic deposition site and the original
smearing function. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochScaleReports
open Function Filter Set Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register FVA2.Scale MS MS.Land
open scoped Topology BigOperators Classical

private theorem scaled {e : ℕ} {f : ℝ → ℂ} (a : ℂ) (h : Price e f) :
    Price e (fun ν => a*f ν) := by
  simpa only [zero_add] using (Price.of_constant a).mul h

private theorem joined {I : Type*} {e : ℕ} (s : Finset I) (f : I → ℝ → ℂ)
    (h : ∀ i ∈ s, Price e (f i)) : Price e (fun ν => ∑ i ∈ s, f i ν) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Price.of_constant (0:ℂ)).widen (q:=e) (Nat.zero_le _)
  | @insert j s hj ih =>
    have q := (h j (Finset.mem_insert_self ..)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa only [max_self,Finset.sum_insert hj] using q

variable {G : Gauge} {hG : G.Simple} (Z : WilsonPrescription G)
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
  {n d : ℕ} (p : Tags G d n) (k : ℕ)

def gap (ν : ℝ) (i : Mesh × Test n) : ℂ :=
  Reg.Pivot.posted ν Z.scheme S d i.1 k n i.2 p - Reg.CoverTest.Rates ν T d k n i.2 p

include M
theorem original : MS.Logarithm.Ready (gap Z (T:=T) (S:=S) p k) := by
  obtain ⟨e,purchase⟩ := FVA2.Scale.Known.serves Z.scheme S p (id : Sample n → Sample n) k
  have samples (v : Sample n) : Price e (fun ν=>Dframe.postedPoint ν Z.scheme S d v k p) := by
    simpa only [Reg.Point.story,PowerSeries.coeff_mk,id_eq] using purchase v
  have posted (m : Mesh) (f : Test n) :
      Price e (fun ν => Reg.Pivot.posted ν Z.scheme S d m k n f p) := by
    simp_rw [Reg.CoverTest.price_m m _ Z.scheme S f k p]
    unfold Deposit
    apply scaled
    apply joined
    exact fun x _ => scaled _ (samples ⟨m,m.back x,0⟩)
  have hs := M.details.toServed.toPosted.toQuoted.toContract.toMission.toSchemeV.born.1
  have limit (f : Test n) : Price e (fun ν => Reg.CoverTest.Rates ν T d k n f p) := by
    apply Price.stride (F:=Front) (Eventually.of_forall (fun m => posted m f))
    exact fun ν => Reg.CoverTest.covered ν Z.scheme S T hG hs n f p
  apply WilsonEpochScalePolynomials.finite
    (f:=fun i : Mesh × Test n => fun t => gap Z (T:=T) (S:=S) p k t i)
  refine ⟨e,fun i => ?_⟩
  simpa only [gap,sub_eq_add_neg,max_self] using (posted i.1 i.2).add (limit i.2).neg

end YM.Integration.WilsonEpochScaleReports
end
