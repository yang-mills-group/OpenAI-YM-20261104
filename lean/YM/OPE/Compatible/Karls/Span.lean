import YM.OPE.Compatible.Karls.Elm
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{W:Fin s→Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {P:ℕ→Mints E→L[ℝ] Mints E}{X:Mints E→L[ℝ] Mints E}
open Quit.PriceZ
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
variable {q y e z:ℝ}
lemma Eave.towns (K:Eave L X T a r q u k)(i:H)(Q:ℕ→ℕ→Dice (Mints E))(C':ℕ→Dice (Mints E))(Y:Punch Q (L i) C' X y e z)(h:z < μ k * μ k)(x w:Lingo r (L i))(hp:0 < μ k):
    Thick (μ k*μ k) (fun j=> Q 0 j x.val w.val-Punch.Folio C' X hp s (((portC X (μ k) s)^j) (K.PO i x)) (((portC X (μ k) s)^j) (K.PO i w))) := by
       let f:=race (L i) 0 x.val; let g:= race (L i) 0 w.val; exact Y.Shelter _ _ _ _ hp h K.ThetaPitch K.trot f g (fun j=> (show f (j+1)=L i j (f j) from (propel (L i) x.val j |>.trans (add_zero _)))) (fun j=> (show g (j+1)=L i j (g j) from (propel (L i) w.val j|>.trans (add_zero _)))) (K.PO i x) (K.PO i w) (K.taleF i x) (K.taleF i w)
end YM.OPE.Hark
