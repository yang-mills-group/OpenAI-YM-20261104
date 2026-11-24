import YM.OPE.Compatible.Grotto.Pipe
/-!
# Angular phase spectra.Lifting station members multilinearly. erased.B.
-/
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
def Busy (L:H→ℕ→ Mints E→L[ℝ] Mints E)(g:H→ℕ→ Mints E)(i:Fin s)(x:H)(n:ℕ):E i:= L x n (fore (g x n) i.val) i
lemma Busy.toll (i:Fin s) (hl:TameP 1 a 1 L)(ha:1≤ a)(hw:0 ≤ w)(h:TameK i.val r a w g): TameP r a w (Busy L g i):=by -- i name use binder
     have ht: TameP (r*1) a w (Busy L g i):= TameP.cast (proj i) (TameP.byOp (TameK.take h ha hw) hl); rwa [mul_one] at ht
-- scalar recurrence folding
abbrev gr (L:H→ℕ→ Mints E→L[ℝ] Mints E)(x:H)(i:Fin s)(n:ℕ):=stride (L x n) i
abbrev te (g:H→ℕ→ Mints E)(x:H)(i:Fin s)(n:ℕ):=g x n i
lemma eleg (he:∀ i n,Edgewise (L i n))(x:H)(j:Fin s)(hg:Run (L x) (g x) (f x)):Run (gr L x j) (te g x j) (fun i=> (Busy L g j x i)+ f x i j):=by
     intro i; unfold gr te; rw [hg,Pi.add_apply,peb (L x i) _ j (he x i),add_assoc];rfl
variable (ht:∀ i n,Assist T (L i n))(hp:TameP 1 a 1 L)(ha:1 ≤ a)(hw:0 ≤ w)(hr:∀ i, ShadeR (T i) k r)
variable {t:ℝ}
include ht hp ha hw hr
variable [∀ i,CompleteSpace (G i)]
lemma Folk (hb:∀ i,Run (L i) (g i) (f i))(hf:TameP r a w f)(hv:Wealth (fun i=>g i 0) a w)(hs:∀ i,∃ C,Hex t (g i) C)(he:∀ i,ShadeR (T i) k t)(hh:r≤ t) : TameP r a w g:=by
     suffices H : ∀ i:ℕ,i ≤ s → TameK i r a w g by exact TameK.all (H _ le_rfl) ha hw
     intro i hi; induction i with
     | zero=> exact fun j hj=> by omega
     | succ n ih=>
          have he':=ih (by omega); intro j hj; by_cases hx:j.val=n; swap;· exact he' j (by omega)
          let P:= Busy L g j; let A:= P + fun i m=> f i m j; have hA(x):Run (gr L x j) (te g x j) (A x):=eleg (fun i m=> (ht i m).arum) x j (hb x); obtain ⟨c,hc,hC⟩:= (TameP.plus ha hw (Busy.toll j hp ha hw (show TameK j.val r a w g from hx.symm ▸ he')) (TameP.cast (proj j) hf) : TameP r a w A); obtain ⟨B,Hb,Hx⟩:= CutR (T j) (hr j) (he j) hh; let z(i:H):=‖g i 0 j‖; refine ⟨fun i=>B*(z i+c i),scaleD (k:=B) (a:=fun i=>z i+c i) (anthW ha hw (normW (aimW (proj j) hv)) hc),fun i=>?_ ⟩ -- params
          obtain ⟨y,hy⟩:= hs i; exact Hx _ (fun n=> (ht i n).gait j) _ _ _ (c i) (hC i) (hA i) (hy.invoke (proj j)) -- t.
end YM.OPE.Hark
