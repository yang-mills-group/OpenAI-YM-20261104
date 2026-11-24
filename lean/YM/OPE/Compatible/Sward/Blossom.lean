import YM.OPE.Compatible.Sward.Fief
import YM.OPE.Compatible.Streams.Feud
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
section
open Finset
variable (P:ℕ→ Mints E→L[ℝ] Mints E)(hp:∀ i,Assist T (P i))(f:ℕ→Mints E)(hf:Run P f 0)
include hp hf
lemma ser (hr:v<r)(hg:Hex 1 P x)(hv:∀ i:Fin s,∀ n,f n i∈ (T i).flag d):∃ b:ℝ, Hex r f b:=by
       let Z: Unit→ℕ→Mints E:=fun _=>f; let p:Unit→ℕ→ Mints E→L[ℝ] Mints E:=fun _=>P; have he :TameP (M:=Unit) 1 1 1 p:=⟨fun _=>x,we0 _ rfl,fun _=> hg⟩ -- wealth const
       have ht(k): k ≤ s→ TameK k r 1 1 Z:=by
          intro ht; induction k with
          | zero=> intro i hi;omega
          | succ i ih=>
             intro j hj; by_cases hy:j.val=i; swap; · exact ih (by omega) j (by omega)
             have hh:=ih (by omega); obtain ⟨b,hb,hB⟩:=Busy.toll j he le_rfl zero_le_one (g:=Z) (w:=1) (show TameK j.val r 1 1 Z from hy.symm ▸ hh)
             let G:= Busy p Z j (); let V:=T j; have hz := eleg (L:=p) (g:=Z) (f:=0) (fun a b=> (hp b).arum) () j hf
             have hL:Run (gr p () j) (te Z () j) G:=by simpa only [Pi.zero_apply,add_zero] using! hz
             let a:=max (‖f 0 j‖) (b ()/(r-v)); refine ⟨fun _=>a,we0 _ rfl,fun x=>?_⟩; apply Run.gap hr a (T j|>.fast) (le_max_right ..) (hB ()) hL (fun i=>(hp i).gait j|>.march (f i j) (hv j i)) (le_max_left ..)
       obtain ⟨c,hc,hz⟩:= (ht s le_rfl).all le_rfl zero_le_one; exact ⟨c (),hz ()⟩
where we0 (r:ℝ)(_h:r=r): Wealth (fun _:Unit=>r) 1 1:= by refine ⟨‖r‖,norm_nonneg _,0,fun i=>?_⟩; simp
end
end YM.OPE.Hark
