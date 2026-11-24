import YM.FormalBulk08.Reef.Mouth

/-! Finite stage with chosen prescription (no final masks).
The separate proof of infinite exponential reach is used through gamma_ready.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free Work.F08 Work.F05 Stationary Tree Wilson
open Series Jets Wick Orb PowerSeries Matrix UVExtension.Free Flat
open scoped Topology BigOperators Matrix ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {K : KernelChoices} {j t : ℕ}
variable (P : Flight j t) (ρ : ChartRatio G)
-- classical decisions baked in Flat.Power etc.
open scoped Classical
abbrev floor (K : KernelChoices) (P : Flight j t) (L : Lodge P.patch) (c : Side) := Lodge.forest (S:=primary P.patch K c) L
def puppet (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) :=
    let S:=primary P.patch K c; let M:=gamma G K P L h
    Matrix.submatrix (M.acts c) (L.splitting (S:=S)) (L.splitting (S:=S))
lemma honey (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) :
   let T := testPrecision G (primary P.patch K c) (floor K P L c) P.wing
   T.PosDef ∧ T*puppet P h L c=1 := (gamma_ready G K P L h).2 c

private def trans_pos {A : Type*} [Fintype A] [DecidableEq A] (T Q : Matrix A A ℝ) (ht : T.PosDef) (he : T*Q=1) :
   Saddle ℝ A := by
   have hh : Tᵀ=T := by ext i j; exact (ht.isHermitian.apply i j)
   have hp : Qᵀ=Q := by
      have hx : Qᵀ*T=1 := by nth_rw 1 [← hh]; rw [←Matrix.transpose_mul,he, Matrix.transpose_one]
      exact left_inv_eq_right_inv hx he
   exact ⟨Q,T,fun i j=> congr_fun (congr_fun hp j) i,fun i j=>congr_fun (congr_fun hh j) i,he⟩

def ferry (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) : Hull (Pine G _ (floor K P L c)) (wire G c) :=
    let q:=puppet P h L c
    { saddle:= trans_pos (testPrecision G (primary P.patch K c) (floor K P L c) P.wing) q (honey P h L c).1 (honey P h L c).2
      drift:= draught (pMean G K P c (floor K P L c))
      main:=crunch (kernelP G K.penalty P.land c) }

lemma consolidate (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side)
    (hr : LocalRatio ρ) (k : (primary P.patch K c).Choices) (p : Pap (wire G (c*P.patch.L))) (hp : coeff 0 p=crunch (kernelP G K.penalty P.wing _)) (ht : 4≤t) : Solved (ferry P h L c) (flush (floor K P L c) k ρ p) := baked G _ P c (floor K P L c) ht h ρ hr k (ferry P h L c).saddle rfl p hp

def landed (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) (k : (primary P.patch K c).Choices) (p : Pap (wire G (c*P.patch.L))) : Pap (wire G c):=
   out (ferry P h L c) (flush (floor K P L c) k ρ p)
lemma landed_cost (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) (k : (primary P.patch K c).Choices) (p : Pap (wire G (c*P.patch.L))) (hp : coeff 0 p=crunch (kernelP G K.penalty P.wing _)) (hr : LocalRatio ρ) (ht : 4≤t) : coeff 0 (landed P ρ h L c k p)=crunch (kernelP G K.penalty P.land c) := out_main _ _ (consolidate _ _ h L _ hr k p hp ht)
lemma landed_choice (h : P.patch.Branches K G) (L : Lodge P.patch) (c : Side) (k r : (primary P.patch K c).Choices) (p : Pap (wire G (c*P.patch.L))) : landed P ρ h L c k p=landed P ρ h L c r p := by
   unfold landed flush vacuumU; rw [clash (primary P.patch K c) h k r]
end YM.FormalBulk08.Reef
