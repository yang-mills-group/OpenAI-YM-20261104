import YM.Integration.WilsonFiniteIncomingMarkedWinding
import YM.WilsonCoeffUV.Kinetic.Base

/-! The full finite Wilson trajectory and the periodized cover vacuum have
exactly the same free angular tensor at every age, on every side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteVacuumFreeInput
open Function Filter Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open Gauge Power Next.Free FreeResolvent Work.F08
open scoped Classical BigOperators
variable {G : Gauge}

theorem agrees (L : Levels G) (β : ChartRatio G) (simple : G.Simple) (hβ : LocalRatio β)
    {m N : ℕ} (hm : m ≤ N) (n : Side) (r : ℕ) :
    (story L β N m).1 n 0 r = emera (actionW L β N m) n 0 r := by
  have finite := ((old L β simple hβ N m hm).basis n).stem
  have cover := (catchment L β simple hβ hm).readout
  cases r with
  | zero =>
    rw [congr_fun finite 0]
    exact shine_dark (by omega)
  | succ r =>
    change (story L β N m).1 n 0 (r+1) = lagoon (actionW L β N m 0 (r+1)) n
    rw [congr_fun finite _,congr_fun cover _]
    by_cases h : r+1 = 2
    · have h1 : r = 1 := by omega
      subst r
      rw [shine_lit,shine_lit]
      obtain ⟨s,C,pos,_,ports⟩ := forms_tail L.clock.kernel.penalty L.clock.kernel.penalty_pos _
        (L.clock.adm m)
      exact (plain_act G n ((ports L m rfl rfl).1 N) pos.le).symm
    · rw [shine_dark (Ne.symm h),shine_dark (Ne.symm h),lagoon_none]

theorem original {e m : ℕ} {E : Credit} (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m)
    {s : ℝ} (hs : 0 < s) :
    ∃ V : ℝ, 1 ≤ V ∧ ∀ N, m < N → ∀ (n : Side) (r : ℕ), Sight
      ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) 0 r)
      (actionW Q.draws Q.paid N (m+1) 0 r) (holt Q m hm s hs).s V := by
  let V := admissionA (Q.mint m hm).gear e * Q.cash (costXV G e E) m
  refine ⟨V,one_le_mul_of_one_le_of_one_le (admissionSeal _) (Credit.purchase _ (Q.depth _ hm)),?_⟩
  intro N cut n r
  rw [agrees Q.draws Q.paid Q.hG Q.green cut]
  exact (cloVent Q m N n hm cut s hs).fare 0 (Nat.zero_le _) r

end YM.Integration.WilsonFiniteVacuumFreeInput
end

