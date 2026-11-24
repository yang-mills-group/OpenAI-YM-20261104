import YM.OPE.Compatible.Streams.Eden
/-! # exact stage advance for virtual flag. -/
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
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{w' p':V→ℝ}
variable (r t:ℕ→ℝ)
section Aeon
variable (A:Aeon V T X w') (J:∀ i,i<d→Eave L X T a (r i) (t i) u i)
include A J
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][∀ i,FiniteDimensional ℝ (G i)]
lemma Aeon.enroll (q:ℕ)(he:q≤d)(hp:0 ≤ p'): Aeon.Vent A q p':=by
    induction q with
    | zero=>
       intro i g h hh; let f(j:V): Mints E:= Pi.single i (g j); have ht(j): f j∈ A.flag 0 j:=by rw[A.first];exact Submodule.mem_top
       exact ⟨fun j=>⟨f j,ht j⟩,aimW (ContinuousLinearMap.single (R:=ℝ) E i) h,fun j=>⟨nt i _,Pi.single_eq_same ..⟩⟩
    | succ q ih=> exact A.vouchers (J q he) hp (ih (by omega))
lemma Aeon.zark (k:ℕ)(he:k <d)(hp:0≤p')(f:V→Fruition X (μ k))(hf:Wealth (fun i=>(f i).val) w' p')(i:ℕ)(ht:i≤s)(hs:∀ j,trims i (f j).val):
     ∃ x:(j:V)→ A.flag k j, Wealth (fun j=>(x j).val) w' p'∧∀ j,trims i (x j).val ∧ A.read k he j (x j)=f j:=by
       induction ht using Nat.decreasingInduction generalizing f with
       | self=> exact ⟨0,wealthZ w' p',fun j=> ⟨fun i _=>rfl,by rw [Pi.zero_apply,map_zero]; exact Subtype.ext (hs j).limb.symm ⟩⟩
       | of_succ n hn IH=>
           let i:Fin s:=⟨n,hn⟩; let Z(j:V):=(T i).Tap k ((f j).val i); let p(j):=(T i).lift k he (Z j); let Q:=J k he; have hx(j): p j∈ (T i).flag k ∧ (T i).Tap k (p j)=Z j:= (T i).rises k he _
           obtain ⟨v,hv,hX⟩:= Aeon.enroll r t A J k (by omega) hp i p (aimW _ (aimW _ (aimW (proj i) hf))) (fun i=>(hx i).1); let F(j):=f j-A.read k he j (v j); have hh(i):=A.quake k he i (v i) (z:= (⟨n,hn⟩)) (hX i).1; have ht(j):trims (n+1) (F j).val:=by
                 apply (Eave.Vita Q (n+1) hn).1; intro z he; by_cases hv:z=i; swap
                 · exact (Eave.Vita Q n hn.le).2 (trims.sub (hs j) (hh j|>.2.1)) _ (Nat.lt_of_le_of_ne (by omega) (fun hx=> hv (Fin.ext hx))) -- instance ambiguity
                 subst z; change (T i).Tap k (_-_)=_; erw [map_sub,(hh j).2.2,(hX j).2,(hx j).2]; exact sub_self _
           obtain ⟨x,h,hP⟩:=IH F (subW A.non hp hf (A.bulk he v hv)) ht; refine ⟨x+v, anthW A.non hp h hv,fun j=>⟨trims.plus ((hP j).1.drop (Nat.le_succ n)) (hX j).1,?_⟩⟩; rw [Pi.add_apply,map_add,(hP j).2]; unfold F; abel
end Aeon
end YM.OPE.Hark
