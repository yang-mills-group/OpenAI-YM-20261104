import YM.Integration.WilsonOriginalPointCompactProgram
import YM.QuadraticLocal.Class.Foundry

/-! Each complete nominal face is the sum of its actual separately published unary sources. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPointCompactFaces
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)
local notation "J" => Stock.census (Fin 3)
local notation "oneC" => Stock.census Unit
local notation "M" => rows owner grades sites T A charge
local notation "own" i:max => (T i).rows (home sites (owner i)) (alone A (owner i))
local notation "atOwn" i:max t:max => subject A (owner i) t

omit [Fintype I] in
def amount (i:I) (g:ℝ) (t:Wallet A) (U:Config G n) : ℂ :=
  charge i * (Spill.Foundry.uncut (own i) g (atOwn i t) U).part ((oneC).fire ())

theorem original (g:ℝ) (t:Wallet A) (U:Config G n)
    (shared:Summable (fun k=>Spill.raw M g t k U))
    (held:∀i:I,Summable (fun z=>Spill.raw (own i) g (atOwn i t) z U)) :
    Spill.Foundry.uncut M g t U=∑i:I,Poly.send ((J).fire (owner i))
      (amount owner grades sites T A charge i g t U) := by
  classical
  change (∑'k:Σi,(T i).Roster,Spill.raw M g t k U)=_
  rw [shared.tsum_sigma,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  have summable:Summable (fun z:(T i).Roster=>Spill.raw M g t ⟨i,z⟩ U):=
    shared.comp_injective (i:=Sigma.mk i) (fun _ _ h=>eq_of_heq (Sigma.mk.inj h).2)
  ext s
  rw [Poly.share summable,Poly.part_send]
  unfold amount Spill.Foundry.uncut
  rw [Poly.share (held i)]
  simp only [Spill.raw]
  change (∑'z:(T i).Roster,(Poly.send ((J).fire (owner i))
      ((M ⟨i,z⟩).nominal g t U)).part s)=
    if s=(J).fire (owner i) then charge i*(∑'z:(T i).Roster,
      (Poly.send ((oneC).fire ()) (((own i) z).nominal g (atOwn i t) U)).part ((oneC).fire ())) else 0
  simp only [Poly.part_send,if_true]
  by_cases h:s=(J).fire (owner i)
  · simp only [h,if_true]
    rw [←tsum_mul_left]
    exact tsum_congr (fun z=>WilsonOriginalPointCompactRoster.nominal owner grades sites T A charge ⟨i,z⟩ t g U)
  · simp [h]

end YM.Integration.WilsonOriginalPointCompactFaces
