import YM.OPE.Compatible.Spa.Plea
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
structure Pipes (A:ℕ→ M→ Submodule ℝ E)(Y:M→ Submodule ℝ E)(X:(e:Fin d)→(m:M)→ A e.val m →ₗ[ℝ] (Jewel (V e)))(g:E→ₗ[ℝ] E)(R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m):Prop where
     top t:A 0 t=⊤
     order (i:ℕ)(he:i<d)(m:M): A (i+1) m≤ A i m
     lower (e:Fin d)(m:M)(v:A e.val m): X e m v=0↔ v.val∈A (e.val+1) m⊔Y m
     toll (e:Fin d)(m:M)(q): X e m (R e m q)=q
     spirit(e:Fin d)(m:M)(q):g (R e m q|>.val)= (R e m (τΓ (V e) q)).val
     sings(e:Fin d)(m:M)(x:E)(h:x∈A (e.val+1) m):g x∈A (e.val+1) m
     sip(m:M)(x:E)(h:x∈Y m):g x∈Y m
abbrev Mel (V:Fin d→Type):= (i:Fin d) → Jewel (V i)
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
abbrev Bay (A:ℕ→ M→ Submodule ℝ E)(Y:M→ Submodule ℝ E)(i:ℕ)(m:M):=A i m⊔Y m
noncomputable def bulk (R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m)(m:M): Mel V →ₗ[ℝ] E := ∑ e: Fin d,(A e.val m|>.subtype).comp ((R e m).comp (LinearMap.proj e))
lemma bulk_way (v:Mel V)(m:M):bulk R m v=∑ i,(R i m (v i)).val:=by rw[bulk,LinearMap.sum_apply];rfl
lemma bulk_single (m:M)(e:Fin d)(v:Jewel (V e)):bulk R m (Pi.single e v)=(R e m v).val:=by rw [bulk_way]; rw[sum_eq_single e]; simp; intro i _ hi; rw[Pi.single_eq_of_ne hi,map_zero]; rfl; simp
include H
lemma depth (m:M){k j:ℕ}(hj:j≤d)(he:k≤j):A j m≤ A k m:=by induction j,he using Nat.le_induction with|base=>rfl|succ j h ih=> exact (H.order j (by omega) m).trans (ih (le_trans (Nat.le_succ _) hj))
lemma cliff (m:M)(k j:ℕ)(hj:j≤d)(he:k≤j):Bay A Y j m≤ Bay A Y k m:= sup_le_sup_right (H.depth m hj he) _
lemma burst (m:M)(x:Mel V)(p:ℕ)(hx:trims p x): bulk R m x∈ A p m:=by
      rw[bulk_way]; refine Submodule.sum_mem _ fun i _=>?_ ; by_cases h:p≤ i.val; exact H.depth m i.isLt.le h (R i m (x i)|>.property)
      rw[hx i (by omega), map_zero]; exact (A p m).zero_mem
-- if ∑ ∈Bay i then leading grade<i van.
lemma torn (m:M)(x:Mel V)(p:ℕ)(hp:p≤d)(h:bulk R m x∈Bay A Y p m): trims p x:=by
     induction p with
     | zero=> exact trims.be _
     | succ p ih=>
       let i:Fin d:=⟨p,by omega⟩; let u:= R i m (x i); have hh:= ih (Nat.le_trans (Nat.le_succ _) hp) (H.cliff m p (p+1) hp (Nat.le_succ p) h)
       let q:Mel V:= Pi.single i (x i); have hx: trims p q:= fun j hj=> Pi.single_eq_of_ne (show j≠ i from (ne_of_lt (by exact show j.val < i.val from hj))) _; have hQ: trims (p+1) (x-q):=by
          apply (trims.up i  (trims.sub hh hx) ?_); rw [Pi.sub_apply, show q i=x i from Pi.single_eq_same ..,sub_self]
       have hg:= H.burst m _ _ hQ; have heq: u.val∈Bay A Y (i.val+1) m:=by rw [show u.val =bulk R m x-bulk R m (x-q) from ?_]; exact Submodule.sub_mem _ h (le_sup_left (a:=A (p+1) m) hg); rw [map_sub,sub_sub_cancel,show bulk R m q=u.val from bulk_single ..] -- eq triangle
       exact trims.up i hh ((H.toll i m _).symm.trans ((H.lower i m u).2 heq))
end Pipes
end YM.OPE.Hark
