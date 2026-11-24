import YM.OPE.Compatible.Streams.Heel
/-! # Wheel.Trans ports for B horizons -/
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
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {X:Mints E→L[ℝ] Mints E}
namespace Eave
variable {θ:ℝ}(U:Eave L X T a r θ u k)(W:H)
include U W
variable [∀ i,CompleteSpace (G i)]
lemma gatherR (p:ℝ)(q:ℝ)(k':ℕ)(hT:∀ i,ShadeR (T i) k' p)(hq:∀ i,ShadeR (T i) k' q)(he:p≤q): Lingo q (L W) ≤ Lingo p (L W):=by
     intro x hx; let w:Unit→H:=fun _=>W; let P:Lingo q (L W):=⟨x,hx⟩; let V:Unit→ℕ→ Mints E:= fun _=> race (L W) 0 x; have hA:=U.annex w; have hU(i:Unit): Run (L (w i)) (V i) 0:=propel _ x; have ht:= Folk (g:=V) hA.HP hA.Yi.1 hA.fits (show (0:Unit→ℝ)≤1 from zero_le_one) hT (show ∀ i: Unit, Run ((L∘w) i) (V i) ((0:Unit→ℕ→Mints E) i) from hU) (zeroP (a∘w) 1 p) (wealthC x) (fun _=>hx) hq he; obtain ⟨c,h,hX⟩:=ht; exact ⟨_,hX (Unit.unit)⟩
lemma Shade_eq (p:ℝ)(k':ℕ)(hT:∀ i,ShadeR (T i) k' θ)(hq: ∀ i,ShadeR (T i) k' p): Lingo θ (L W)= Lingo p (L W):=by
      let v:Fin s:=⟨0,U.nonempty⟩; have ht:0 ≤ p:=(T v).fast.trans (hq v|>.Fast.le); rcases le_total θ p with h|h; exact le_antisymm (fun i h'=>by obtain ⟨c,hF⟩:=h'; exact ⟨c,Hex.warm hF U.ThetaPitch h⟩) (U.gatherR W θ p k' hT hq h); exact le_antisymm (U.gatherR W p θ k' hq hT h) (fun i h'=>by obtain ⟨c,hF⟩:=h'; exact ⟨c,Hex.warm hF ht h⟩)
omit U
lemma wheel (U:Eave L X T a r θ u 0)(p:Mints E) : p ∈ Lingo r (L W):=by
       obtain ⟨f,h,hF⟩:= U.Yi.1; have hp := show 0 ≤ f W from (hF W).price; let v:= max (f W) r; have hh(p:Mints E):Hex v (race (L W) 0 p) ‖p‖:=by
             intro n; have hx:0 ≤ v:=hp.trans (le_max_left ..); induction n with
             | zero=> simp only [pow_zero,mul_one,race,le_rfl]
             | succ i ih=> rw [propel (L W) p,Pi.zero_apply,add_zero]; have h':‖L W i‖ ≤ v:=by apply (hF W i).trans; unfold v; simp
                           exact ((le_opNorm ..).trans ((mul_le_mul h' ih (norm_nonneg _) hx))).trans_eq (by ring)
       have ht(j:Fin s): ShadeR (T j) 0 v:=⟨(U.slope j).Fast.trans_le (le_max_right ..),Nat.zero_le _,fun _ he=> by omega,fun k h he=>(U.slope j).brisk k h he|>.trans_le (le_max_right ..)⟩
       exact U.gatherR W _ v 0 U.slope ht (le_max_right ..) (show p∈Lingo v (L W) from ⟨_,hh p⟩)
include U
omit [∀ i,CompleteSpace (G i)] in
lemma lights (Q:Lingo r (L W)) (i:Fin s) (hp:trims i.val Q.val) : Q.val i∈(T i).flag k:=by
    let g:= race (L W) 0 Q.val; have hU:=U.slope i; obtain ⟨c,H⟩:=Q.property; have he:= Hark.runT (fun n=>(U.HP W n).arum) (propel _ _ ) i hp; exact inLayer hU.Fast (fun n=> (U.HP W n).gait i) he U.mark.le hU.slow (Hex.invoke (proj i) (show Hex r g c from H))
end Eave
end YM.OPE.Hark
