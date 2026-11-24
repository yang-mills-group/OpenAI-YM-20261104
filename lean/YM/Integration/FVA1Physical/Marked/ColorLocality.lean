import YM.Integration.FVA1Physical.Marked.ColorHistory

/-! Disjoint marker factors can be polarized independently: the actual
transported coefficient of S depends only on the choices inside S. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Multi Qlocal Quipu Quipu.Sonnet Tern Moonset MeasureTheory
open MergeProof.Accent Extra.Trajectories LocalLTE.Sail PhysicalNext.Repeat.Legato.Bandage.Harmonics
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge}

def SlotLocal (A : Finset I→Poly B) : Prop :=
  ∀ (s : B.Mode) (t t' : Finset I), (∀ j∈s.val, j∈t ↔ j∈t') → (A t).part s = (A t').part s

variable [Fintype I] {H : History G} {N n b qd : ℕ} {ξ : I→ℕ} {o : I→Site (H.S.side N n)}
    {P : Rep G (H.S.side N n)} (W : Rooms.Wallet (Finset I) o P B ξ qd b) (cut : ℕ) (g : ℝ)
    (Y : Batch H N n I) (iso : ∀ t (s : Senses B),2 ≤ (essence s).card → W.weight t s=0)
    (dic : ∀ t j v,bareLeaf W t cut g j v=component t j (Y.wavelengths j v))

include iso dic in
theorem bare_slot_local (v : Config G (H.S.side N n)) :
    SlotLocal (fun t=> ((H.rep N n N).eval v:ℂ) • Poly.pass (W.render cut g t v)) := by
  intro s t t' same
  simp only [Poly.part_smul,singleton_render W t cut g (iso t),singleton_render W t' cut g (iso t'),Mach,pass_fire]
  apply congrArg
  apply Finset.prod_congr rfl
  intro j hj
  simp only [dic,component,propext (same j hj)]

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

theorem Delivered.color_local (Y : Batch X.family.path N n I)
    (h : Delivered X ζ K ξ b T o d U z (N:=N) (j:=N) (δ:=δ)) (hz : z ≤ m) (hm : m ≤ N)
    (born : ∀ t v,wallet[N] t v = Poly.pass ((U N).render cut g t v) * Poly.bead B (vac[N] v:ℂ))
    (iso : ∀ t (s : Senses B),2 ≤ (essence s).card → (U N).weight t s=0)
    (dic : ∀ t j v,bareLeaf (U N) t cut g j v=component t j (Y.wavelengths j v))
    (v : Config G (X.family.side m n)) : SlotLocal (fun t=>wallet[m] t v) := by
  let A t := fun u : Config G (X.family.side N n)=> (vac[N] u:ℂ) • Poly.pass ((U N).render cut g t u)
  have live (t) : Integrable (A t) (prior G _) := component_integrable (U N) cut g Y iso dic X.makes.wilson t
  have start (t) : wallet[N] t = A t := by funext u; rw [born,mul_comm,Poly.product_bead]
  intro s t t' same
  have row (i : Finset I) : (wallet[m] i v).part s=gust X.family.path N n N (fun u=>(A i u).part s) m hm v := by
    rw [h.full_path X hz hm i,start]
    exact congrFun (gust_linear (ContinuousLinearMap.proj s : Poly B→L[ℝ]ℂ) X.family.path N n (A i) (live i) hm) v
  have sameBare : (fun u=>(A t u).part s) = fun u=>(A t' u).part s :=
    funext fun u=>bare_slot_local (U N) cut g Y iso dic u s t t' same
  rw [row,row,sameBare]

end YM.Qlocal.Actual.Season.Studio
