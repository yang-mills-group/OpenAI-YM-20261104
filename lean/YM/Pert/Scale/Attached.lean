import YM.Pert.Scale.Window
/-! Exact attachment of the relative-length ledgers to the original kernel. Domain product filter suffices for uniform conclusions on one fixed small window per profile; not claiming the reporting sequence itself has bounded inverse mesh gaps. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000
noncomputable section
namespace YM.Pert.Scale
open Analysis Function Filter Topology Position Maxwell Climb Spec Set Ward Table Org MeasureTheory Next.UVStress
open scoped ContDiff BigOperators
variable {G:Gauge} {C:Family G} {I:Extraction.Order} {S:Table C.book} {d n r : ℕ}
variable (Q : Conditions C.labels d n) (X : Scaling S)
abbrev fromBasis (i : Fin Q.slots) (a : inklet Q i) (j : Fin (Q.arity i)) := baring C.labels d (a j)
def cloud (k : ℕ) (v : ℝ) (i : Fin Q.slots) (z : inklet Q i) :=
  ∫ x : Points (Q.arity i), Q.profiles i x * swivel X k (fromBasis Q i z) (v • x)
def waxProfile (p : Fin r → E C.labels d) := disc (fun j => (⟨d,p j⟩:(freeTable C.labels).Tag))
def wax (v : ℝ) (i : Fin Q.slots) (z : inklet Q i) :=
  ∫ x : Points (Q.arity i), Q.profiles i x * waxProfile (C:=C) (fromBasis Q i z) (v • x)
variable {X} {b:Final C I S} (h : FirstExtension b X)
include h in
lemma follows' (p : Fin r→E C.labels d) :
   Follows (fun i=> swivel X i p) (waxProfile (C:=C) p) := by
  let v := (fun j => (⟨d,p j⟩:(freeTable C.labels).Tag))
  haveI : IsBoundedSMul ℝ (Points r) := .of_norm_smul_le NormedSpace.norm_smul_le
  haveI : ContinuousSMul ℝ (Points r) := IsBoundedSMul.continuousSMul
  have hX (k) : ContDiff ℝ ∞ (fun x : Points r=> X.r k • x) := ((X.r k • ContinuousLinearMap.id ℝ (Points r) : Points r →L[ℝ] Points r)).contDiff
  exact ⟨fun k=> (smoothDisc b.room.kernel.smooth _).comp (hX k).contDiffOn (fun _=> slides (X.positive k)), smoothDisc (table_smooth _) _,
    fun j K hK hsep δ hd => by
      have he := h.jets r j v (fun _=>false) (fun _=> (⟨0,0⟩:Axis×Axis)) hK hsep hd
      have h1 : freeWithStress C.labels v (fun _ => false) (fun _ => (⟨0,0⟩:Axis × Axis)) = v := by ext1 i; rfl
      have h2 k : scaledPhysical X b.sector.energy k v (fun _ => false) (fun _ => (⟨0,0⟩:Axis × Axis)) = fun i=> (⟨d,(X.U k d) (p i)⟩:S.Tag) := by ext1 i; rfl
      simp only [h1,h2] at he
      exact he⟩

lemma wax_one : wax Q 1 = white Q := funext fun i => funext fun z => by simp only [wax,one_smul,white,fromBasis,waxProfile]
include h in
theorem cloud_tends (hv : CleanProfiles Q) {s : ℝ} (hs : 0<s) :
   Tendsto (Function.uncurry (cloud Q X)) (atTop ×ˢ 𝓝 s) (𝓝 (wax Q s)) := by
  apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro z
  obtain ⟨t,ht⟩ := hv i
  simp only [uncurry_apply_pair,uncurry_def,cloud,wax,← ht]
  exact (follows' h _).value t hs
-- Use these actual centers and leading array derivatives *as finite scale parameters*, not themselves the asymptotic coupling.
def turnedSlope (k : ℕ) (s : ℝ) (i : Fin Q.slots) (z : inklet Q i) :=
   ∫ x : Points (Q.arity i), Q.profiles i x * fderiv ℝ (swivel X k (fromBasis Q i z)) (s • x) x
def waxSlope (s : ℝ) (i : Fin Q.slots) (z : inklet Q i) :=
   ∫ x : Points (Q.arity i), Q.profiles i x * fderiv ℝ (waxProfile (C:=C) (fromBasis Q i z)) (s • x) x
include h in
lemma cloud_deriv (hv : CleanProfiles Q) (k : ℕ) {s : ℝ} (hs : 0<s) :
    HasDerivAt (cloud Q X k) (turnedSlope Q (X:=X) k s) s := by
  apply hasDerivAt_pi.mpr; intro i; apply hasDerivAt_pi.mpr; intro z
  obtain ⟨t,ht⟩ := hv i
  simp only [cloud,turnedSlope,←ht]
  exact shift_deriv t ((follows' h _).actual k) hs
lemma wax_deriv (hv : CleanProfiles Q) {s : ℝ} (hs : 0<s) :
    HasDerivAt (wax Q) (waxSlope Q s) s := by
  apply hasDerivAt_pi.mpr; intro i; apply hasDerivAt_pi.mpr; intro z
  obtain ⟨t,ht⟩ := hv i
  simp only [wax,waxSlope,←ht]
  exact shift_deriv t (smoothDisc (table_smooth _) _) hs
include h in
theorem cloud_turns (hv : CleanProfiles Q) {s : ℝ} (hs : 0<s) :
     Tendsto (fun k : ℕ => turnedSlope Q (X:=X) k s) atTop (𝓝 (waxSlope Q s)) := by
  apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro z
  obtain ⟨t,ht⟩ := hv i
  let he := (follows' h (fromBasis Q i z))
  simpa only [(shift_deriv t he.lead hs).deriv,(shift_deriv t (he.actual _) hs).deriv,
    turnedSlope,waxSlope,←ht,shiftLead] using he.slope t hs
end YM.Pert.Scale
