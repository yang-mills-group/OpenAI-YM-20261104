import YM.Integration.FVA1Physical.Marked.ComplexChannels
import YM.Integration.FVA1Physical.Marked.WalletPath

/-! The source polarization commutes with all stages of the true physical
block map. Each real channel is independently integrable on its own masks. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Marker Multi Qlocal Quipu Quipu.Sonnet Tern Moonset MeasureTheory
open MergeProof.Accent Extra.Trajectories LocalLTE.Sail
open PhysicalNext.Repeat.Legato.Bandage.Harmonics
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {B : Census I} {G : Gauge}

def coloring : (Finset I→Poly B) →L[ℂ] Poly B := ContinuousLinearMap.pi (fun s:B.Mode=>
  ∑ t∈s.val.powerset,Complex.I^t.card •
    ((ContinuousLinearMap.proj s : Poly B→L[ℂ]ℂ).comp (ContinuousLinearMap.proj t)))

omit [Fintype I] in
theorem coloring_apply (A : Finset I→Poly B) : coloring A = complexWallet A := by
  apply Marker.Poly.ext
  intro s
  change ((∑ t∈s.val.powerset,Complex.I^t.card •
    ((ContinuousLinearMap.proj s : Poly B→L[ℂ]ℂ).comp (ContinuousLinearMap.proj t))) A) = _
  simp only [sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rfl

theorem gust_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E→L[ℝ]F) (A : History G) (N n : ℕ) (f : Config G (A.S.side N n)→E)
    (hf : Integrable f (prior G _)) {m : ℕ} (hm : m ≤ N) :
    (fun v=>L (gust A N n N f m hm v)) = gust A N n N (fun v=>L (f v)) m hm := by
  induction hm using Nat.decreasingInduction with
  | self => rw [gust_base,gust_base]
  | of_succ k hk ih =>
    rw [gust_step A N n N f hk,gust_step A N n N _ hk,←ih]
    funext v
    unfold StepData.push
    have hi := StepData.push_slice (A.levels.transition_mass k n (A.β N n (k+1))) v
      (gust A N n N f (k+1) hk) (gust_live A N n N f hf hk)
    exact (L.integral_comp_comm hi).symm.trans (integral_congr_ae (Eventually.of_forall fun _=>L.map_smul _ _))

variable {H : History G} {N n b d : ℕ} {ξ : I→ℕ} {o : I→Site (H.S.side N n)}
    {P : Rep G (H.S.side N n)} (W : Rooms.Wallet (Finset I) o P B ξ d b)
    (cut : ℕ) (g : ℝ) (Y : Batch H N n I)
    (isolated : ∀ t (s : Senses B), 2 ≤ (essence s).card → W.weight t s=0)
    (realized : ∀ t j u,bareLeaf W t cut g j u = component t j (Y.wavelengths j u))

include isolated realized in
theorem component_integrable (selected : H.Selected) (t : Finset I) :
    Integrable (fun v=>((H.rep N n N).eval v:ℂ) • Poly.pass (W.render cut g t v)) (prior G _) := by
  apply integrable_pi_iff.mpr
  intro s
  let K := {v : Config G (H.S.side N n) | ∀ j∈s.val,Healthy P.p.threshold (Tale.court P.p.B (o j)) v}
  have measurable : MeasurableSet K := by
    simp only [K,Set.setOf_forall]
    exact (isClosed_iInter fun j=>isClosed_iInter fun _=>healthy_closed _ _).measurableSet
  let f := fun v=>((H.rep N n N).eval v:ℂ)* ∏ j∈s.val,(component t j (Y.wavelengths j v):ℂ)
  have hv : Continuous (H.rep N n N).eval := by rw [(selected.starts N n).2]; exact bare_cont _
  have hc (j : I) : Continuous fun v=>(component t j (Y.wavelengths j v):ℂ) := by
    unfold component
    split
    · exact Complex.continuous_ofReal.comp (Complex.continuous_im.comp (physicalField_continuous Y j))
    · exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp (physicalField_continuous Y j))
  have continuous : Continuous f := (Complex.continuous_ofReal.comp hv).mul
    (continuous_finsetProd _ (fun j _=>hc j))
  let coeff := fun v=>(((H.rep N n N).eval v:ℂ) • Poly.pass (W.render cut g t v)).part s
  have eq : coeff = K.indicator f := by
    funext v
    change (((H.rep N n N).eval v:ℂ) • Poly.pass (W.render cut g t v)).part s=K.indicator f v
    rw [Poly.part_smul,singleton_render W t cut g (isolated t),Mach,pass_fire]
    by_cases ok:v∈K
    · rw [Set.indicator_of_mem ok]
      congr 1
      exact Finset.prod_congr rfl (fun j hj=>by rw [if_pos (ok j hj),realized])
    rw [Set.indicator_of_notMem ok]
    change ¬∀ j∈s.val,Healthy P.p.threshold (Tale.court P.p.B (o j)) v at ok
    push Not at ok
    obtain ⟨j,hj,bad⟩ := ok
    rw [Finset.prod_eq_zero hj (if_neg bad),mul_zero]
  change Integrable coeff (prior G _)
  rw [eq]
  exact (continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).indicator measurable

end YM.Integration.FVA1Physical.Marked

namespace YM.Qlocal.Actual.Season.Studio
open Filter Lattice RG Wilson Tree Marker Multi Extra.Trajectories RG3.Script.Picnic MeasureTheory
open Pressure ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open Qlocal.Quipu Quipu.Sonnet Tern Parabola Moonset Rooms
open Integration FVA1Physical FVA1Physical.Marked MergeProof.Accent LocalLTE.Sail
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {B : Census I} (X : Run G)
    {N n z m b qd : ℕ} {ξ : I→ℕ} {ζ : ℕ→ℝ} {K : ℕ→ℕ} {T : Ray B} {δ d : ℝ}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)} {o : (i : ℕ) → I→Site (X.family.side i n)}
    {U : (i : ℕ) → Wallet (Finset I) (o i) (x i) B ξ qd b}
local notation "wallet[" i "]" => interpretation (N:=N) X ξ b i (U i)
local notation "vac[" i "]" => (X.family.path.rep N n i).eval
local notation "cut" => Stores.till (X.alloy.B.a.clock.hatBeta N)
local notation "g" => Coat.gStep (X.family.path.β N n N)

/-- The complex reconstruction of the *actual transported* real wallet
is exactly the true block push of its fully reconstructed complex input. -/
theorem Delivered.color_path (Y : Batch X.family.path N n I)
    (h : Delivered X ζ K ξ b T o d U z (N:=N) (j:=N) (δ:=δ)) (hz : z ≤ m) (hm : m ≤ N)
    (born : ∀ t v,wallet[N] t v = Poly.pass ((U N).render cut g t v) * Poly.bead B (vac[N] v:ℂ))
    (iso : ∀ t (s : Senses B),2 ≤ (essence s).card → (U N).weight t s=0)
    (dictionary : ∀ t j v,bareLeaf (U N) t cut g j v=component t j (Y.wavelengths j v)) :
    (fun v=>complexWallet (fun t=>wallet[m] t v)) = gust X.family.path N n N
      (complexSeed (H:=X.family.path) (N:=N) (n:=n) (U N) cut g) m hm := by
  let base := fun v : Config G (X.family.side N n)=>fun t : Finset I=> (vac[N] v:ℂ) • Poly.pass ((U N).render cut g t v)
  have live : Integrable base (prior G _) := integrable_pi_iff.mpr (fun t=>
    component_integrable (U N) cut g Y iso dictionary X.makes.wilson t)
  have eq (t) : wallet[N] t = fun v=>base v t := by
    funext v
    rw [born,mul_comm,Poly.product_bead]
  have row (t) (v) : wallet[m] t v = (gust X.family.path N n N base m hm v) t := by
    rw [h.full_path X hz hm t,eq]
    exact (congrFun (gust_linear (ContinuousLinearMap.proj t) X.family.path N n base live hm) v).symm
  funext v
  simp_rw [row]
  rw [←coloring_apply]
  have restore : (fun u=>coloring (base u)) = complexSeed (H:=X.family.path) (N:=N) (n:=n)
      (U N) cut g := funext fun _=>coloring_apply _
  rw [←restore]
  exact congrFun (gust_linear (coloring.restrictScalars ℝ) X.family.path N n base live hm) v

end YM.Qlocal.Actual.Season.Studio
