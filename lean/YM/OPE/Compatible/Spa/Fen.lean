import YM.OPE.Compatible.Spa.Knew
/-!
# Flag ledger. compressed.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E F Q:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
-- `read F→ Tokens`. Lift provided ζ.Price. specific Veins inputs
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
include H
lemma hexist (p:ℕ)(hp:p≤d)(m:M)(v:E)(h:v∈Bay A Y p m):∃ f:Mel V,v-bulk R m f∈Bay A Y d m:=by
      induction hp using Nat.decreasingInduction generalizing v with
      | self=>exact ⟨0,by rw[map_zero,sub_zero]; exact h⟩
      | of_succ i hi IH=>
         let j:Fin d:=⟨i,hi⟩; obtain ⟨x,hx,y,hy,H'⟩:=Submodule.mem_sup.mp h; let z:A i m:=⟨x,hx⟩; let e:= X j m z; let E':Mel V:= Pi.single j e; have he := bulk_single (R:=R) m j e; have hx' : (z-R j m e).val∈ Bay A Y (j.val+1) m:= (H.lower j m _).1 (by rw[map_sub,H.toll j m e]; exact sub_self _)
         obtain ⟨w,hw⟩:= IH (v-bulk R m E') ((show _ from (by
            rw [show bulk R m E'= (R j m e).val from he,← H',show x+y- (R j m e).val=(z-R j m e).val+y by change _= x-(R j m e).val+y; abel]; exact Submodule.add_mem _ hx' (le_sup_right (a:=A (i+1) m) hy))))
         use E'+w; rw [map_add, ← sub_sub]; exact hw
lemma supplies (m:M):∃ π:E→ₗ[ℝ] Mel V, Sleek (bulk R m) π (Bay A Y d m):=frond _ _ (fun f h=> (H.torn m f d le_rfl h).limb) (fun x=> H.hexist 0 (Nat.zero_le _) m x (by rw [Bay,H.top,top_sup_eq]; exact Submodule.mem_top))
noncomputable def port (m:M): E →ₗ[ℝ] Mel V:=(supplies H m).choose
lemma worthM (m:M): Sleek (bulk R m) (port H m) (Bay A Y d m):=(supplies H m).choose_spec
lemma port_zero (m:M)(p:ℕ)(hp:p ≤ d)(x:E): x∈ Bay A Y p m ↔ trims p (H.port m x):=by
       have he:= H.cliff m p d le_rfl hp (H.worthM m|>.slice x); constructor
       · intro h; apply H.torn m _ p hp; simpa only [sub_sub_cancel] using Submodule.sub_mem _ h he
       intro h; simpa only [sub_add_cancel] using Submodule.add_mem _ he (le_sup_left (a:=A p m) (H.burst m _ p h))
lemma port_grade (e:Fin d)(m:M)(x:A e.val m): H.port m x.val e=X e m x :=by
       let v:= X e m x; have ht:(x-R e m v).val∈ Bay A Y (e.val+1) m:= (H.lower e m _).1 (by rw[map_sub,H.toll]; exact sub_self _); let w:Mel V:=Pi.single e v; have hv : H.port m (x-R e m v).val e=0:=(H.port_zero m (e.val+1) e.isLt _).1 ht e (Nat.lt_succ_self _); rw[Submodule.coe_sub,map_sub,Pi.sub_apply,← bulk_single,H.worthM m |>.len,Pi.single_eq_same] at hv; exact sub_eq_zero.mp hv
lemma onBay (m:M)(x:E)(hx:x∈Bay A Y d m):g x∈Bay A Y d m:=by
      obtain ⟨u,hu,z,hz,h⟩:=Submodule.mem_sup.mp hx; subst x; rw [map_add]; refine Submodule.add_mem _ (le_sup_left (a:=A d m) ?_) (le_sup_right (b:=Y m) (H.sip _ _ hz)); by_cases h:d=0; rw[h,H.top]; exact Submodule.mem_top
      let i:Fin d:= ⟨d-1,(by omega)⟩; have hd: i.val+1=d:=Nat.sub_add_cancel (by omega); exact hd ▸ H.sings _ _ _ (hd.symm ▸ hu)
omit H in
noncomputable def FlowP (V: Fin d→ Type)[∀ i,NormedAddCommGroup (V i)][∀ i, NormedSpace ℝ (V i)]: Mel V→ₗ[ℝ] Mel V:= LinearMap.pi (fun i=> (τΓ (V i)).comp (LinearMap.proj i))
lemma sway (m:M)(x:Mel V): g (bulk R m x)=bulk R m (FlowP V x):=by rw [bulk_way,bulk_way,map_sum]; apply Finset.sum_congr rfl; exact fun i _=> H.spirit i m _
lemma portτ (m:M)(x:E): H.port m (g x)=FlowP V (H.port m x):=H.worthM m|>.comm (FlowP V) (H.onBay m) (H.sway m) x
end Pipes
end YM.OPE.Hark
