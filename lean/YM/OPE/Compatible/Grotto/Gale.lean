import YM.OPE.Compatible.Grotto.Gem
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
lemma runsK {L:ℕ→ Mints E→L[ℝ] Mints E}{f:ℕ→ Mints E}(hp:∀ i,Edgewise (L i))(hf:Run L f 0) (h:trims k (f 0)):∀ i,trims k (f i):=by intro i; induction i with | zero=>exact h | succ i ih=> rw [hf,Pi.zero_apply,add_zero]; exact hp _ _ _ ih
lemma runT {L:ℕ→ Mints E→L[ℝ] Mints E}{f:ℕ→ Mints E}(hp:∀ i,Edgewise (L i))(hf:Run L f 0)(i:Fin s) (h:trims i.val (f 0)): Run (fun n=> stride (L n) i) (fun n=> f n i) 0:=by
    intro n; change f (n+1) i=stride (L n) i _+_; rw [hf,Pi.zero_apply,add_zero,scissor (hp n) i _ (runsK hp hf h n)]; rw [Pi.zero_apply,add_zero]
variable (ht:∀ i n, Assist T (L i n))(hp:TameP 1 a 1 L)(ha:1≤ a)(hw: 0≤ w)(hr:∀ i,ShadeR (T i) k r)
include ht hp ha hw hr
variable [∀ i,CompleteSpace (G i)]
-- Step(s,k). Tune all higher phases.
abbrev sprint (L:H→ℕ→ Mints E→L[ℝ] Mints E)(x:H→Mints E)(i:H):ℕ→ Mints E:= race (L i) 0 (x i)
lemma scout (j:ℕ)(he:j≤s):∀ z:H→Mints E,Wealth z a w→TameK j r a w (sprint L z)→ ∃ y:H→ Mints E, TameP r a w (sprint L y)∧∀ i,trims j (y i-z i):=by
     induction he using Nat.decreasingInduction with
     | self => exact fun z _ hz=>⟨z,hz.all ha hw,fun i=>by rw [sub_self]; exact fun _ _=>rfl⟩
     | of_succ i hx ih=>
        intro z hz hf; let j:Fin s:=⟨i,hx⟩; let f:=sprint L z; let Q:= Busy L f j; obtain ⟨c,hc,hC⟩:= Busy.toll j hp ha hw hf; obtain ⟨b,hb,hB⟩:=solk (T j) (hr j).Fast (hr j).ex 0 (by omega); choose g hg' hg using fun x=>hB (gr L x j) (fun i=> (ht _ i).gait j) (Q x) (c x) (hC x) fun i=> (T j).first _
        let V:=fun x=> race (gr L x j) (Q x) (g x); have hv:TameP r a w V:=⟨fun x=>b*c x,scaleD hc,hg⟩; have he: Wealth g a w:=hv.place 0
        let y:=fun x=> z x+ Pi.single j (g x-z x j); have hy(x):y x j=g x:=by unfold y; rw [Pi.add_apply,Pi.single_eq_same]; abel
        have hm:Wealth y a w:= anthW ha hw hz (aimW (ContinuousLinearMap.single (R:=ℝ) E j) (subW ha hw he (aimW (proj j) hz))); let W:= sprint L y; have hW(x):Run (L x) (W x-f x) 0:=sub_zero (0:ℕ→Mints E) ▸ Run.sub (propel _ _) (propel _ _)
        have hu(x):trims i (y x-z x):=by unfold y; rw [add_sub_cancel_left]; exact nt j _
        have hh(x n):fore (W x n) i=fore (f x n) i:=by
             funext k; have he:= runsK (fun i=>(ht x i).arum) (hW x) (k:=i) (hu x) n; unfold fore; split_ifs with hk; exact sub_eq_zero.mp (he k hk);rfl
        have hZ(x):Run (gr L x j) (te W x j) (Q x):=by
             intro n; have hp:= eleg (g:=W) (L:=L) (f:=0) (fun i n=> (ht i n).arum) x j (propel _ _) n; apply hp.trans; dsimp only []; erw [add_zero]; unfold Busy Q Busy; rw [hh x n]
        obtain ⟨P,hP,H'⟩:=ih y hm (show TameK (i+1) r a w W from by
             intro k ht; by_cases hz:k=j
             · subst k; rw [show (fun x n=> W x n j)= V from funext fun i=> Run.agrees (hZ i) (gait _ _ _) (hy i)]; exact hv
             have he': k.val< i:=by have hh:k.val ≠ i:= Fin.val_injective.ne hz; omega
             rw [show (fun x n=> W x n k)= fun i n=> f i n k from ?_]; exact hf _ he'
             funext x n; have hX := congr_fun (hh x n) k; simpa [fore,he'] using hX ); refine ⟨P,hP,fun i=>?_⟩; rw [show P i-z i=(P i-y i)+(y i-z i) by abel]; exact ((H' i).drop (Nat.le_succ _)).plus (hu _)
lemma pests (i:Fin s)(x:H→ E i)(hX:Wealth x a w)(hT:∀ j,x j∈ (T i).flag k):∃ R:H→Mints E,TameP r a w (sprint L R) ∧∀ j,trims i.val (R j) ∧ R j i=x j:=by
     let z:= fun j=> Pi.single i (x j); let g:=sprint L z; have hp0(x):Run (L x) (g x) 0:=propel _ _; have hx(x):trims i.val (g x 0):=nt i _
     have hp2:TameK (i.val+1) r a w g:=by
        intro j hj; by_cases he:j=i; swap;· rw [show (fun x n=> g x n j)=0 from funext fun x=> funext fun n=> runsK (fun q=>(ht _ _).arum) (hp0 x) (hx x) n j (by have hx:j.val≠i.val:=Fin.val_injective.ne he; omega)]; exact zeroP ..
        subst j; obtain ⟨c,hc,hC⟩:= even (T i) (hr i).Fast (hr i).ex k (hr i).slot (hr i).brisk; refine ⟨_,scaleD (k:=c) (normW hX),fun n=>?_⟩; have hh:g n 0 i=x n:=Pi.single_eq_same ..; have hx:=hC (gr L n i) (fun j=>(ht n j).gait i) (fun t=> g n t i) (runT (fun j=> (ht n j).arum) (hp0 n) i (hx n)) (by rw [hh];exact hT n); change Hex _ _ (c*‖g n 0 i‖) at hx; rwa [hh] at hx
     obtain ⟨y,hY,h⟩:= scout ht hp ha hw hr (i.val+1) i.isLt z (aimW (ContinuousLinearMap.single (R:=ℝ) E i) hX) (show TameK (i.val+1) r a w g from hp2); refine ⟨y,hY,fun j=>⟨?_,(sub_eq_zero.mp (h j i (Nat.lt_succ_self _))).trans (Pi.single_eq_same ..)⟩⟩; rw [show y j=y j-z j+z j from by abel]; exact ((h _).drop (by omega)).plus (nt i _)
end YM.OPE.Hark
