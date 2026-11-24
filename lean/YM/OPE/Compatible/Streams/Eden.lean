import YM.OPE.Compatible.Streams.Eager
/-!
# flag reservations.Kernels.FE. -/
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
-- aeon covers entire tuned leading
namespace Aeon
variable (A:Aeon V T X w') (U:Eave L X T a r x u k) (hp:0≤ p')
abbrev Vent(k:ℕ)(p:V→ℝ):Prop:=∀ i:Fin s,∀ g:V→ E i, Wealth g w' p → (∀ j,g j∈(T i).flag k)→∃ v:∀ j,A.flag k j, Wealth (fun j=>(v j).val) w' p ∧ ∀ j,trims i.val (v j).val ∧ (v j).val i=g j
include hp U
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
lemma skies (h:Vent A k p')(i:Fin s)(m:ℕ)(hi:i.val< m)(hx:m ≤ s) (z:∀ j,A.flag k j)(hj:Wealth (fun j=>(z j).val) w' p')(he:∀ j,trims m ((A.read k U.mark j) (z j)).val):
     ∃ f:∀ j,A.flag k j, Wealth (fun i=>(f i).val) w' p' ∧ ∀ j,trims m (f j).val ∧A.read k U.mark j (f j)= A.read k U.mark j (z j):=by -- solve
       induction hx using Nat.decreasingInduction generalizing z with
       | self=> refine ⟨0,wealthZ w' p', fun j=>⟨fun _ _=>rfl,?_⟩⟩; rw [Pi.zero_apply,map_zero]; exact Subtype.ext (he j).limb.symm
       | of_succ n hn IH=>
           let i:Fin s:=⟨n,hn⟩; let X:=A.read k U.mark
           let F(j):= X j (z j); let t(j):= (T i).Tap k ((F j).val i); let y:V→ E i:=(T i).lift k U.mark ∘ t
           have hv(j): y j∈(T i).flag k ∧ (T i).Tap k (y j)= t j:= (T i).rises _ _ _
           obtain ⟨f,hF,H⟩:= h i y (aimW _ (aimW _ (aimW (proj i) (A.bulk U.mark z hj)))) (fun j=>(hv j).1); let x(j):= z j - f j; have hh(j): trims (n+1) (X j (x j)).val:=by
                have hs:= A.quake k U.mark j (f j) i (H j).1; apply (Eave.Vita U (n+1) hn).1; intro q h
                by_cases hh':q=i; swap
                · have hx:q.val<n:= Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) (fun hx=> hh' (Fin.ext hx))
                  apply (Eave.Vita U n hn.le).2 _ q hx; unfold X x; rw [map_sub]; exact trims.sub (he j) hs.2.1
                subst q; change (T i).Tap k ((X j (x j)).val i)= 0; unfold x; rw [map_sub]; change (T i).Tap k (_-_)= _; erw [map_sub,hs.2.2,(H j).2,(hv j).2]; exact sub_self _
           obtain ⟨g,hG,h⟩:= IH (Nat.lt_succ_of_lt hi) x (subW A.non hp hj hF) hh; refine ⟨f+g, anthW A.non hp hF hG,fun j=> ⟨((H j).1).plus ((h j).1.drop (Nat.le_succ n)),?_⟩⟩; rw [Pi.add_apply,map_add,(h j).2]; unfold x;rw [map_sub]; abel
lemma vouchers (h:Vent A k p'): Vent A (k+1) p':= by
       intro i g he hh; obtain ⟨x,hx,hF⟩:= h i g he (fun j=>((T i).next k U.mark _|>.mp (hh j)).1);
       have hv(j): trims (i.val+1) (A.read k U.mark j (x j)).val:=by
          have hf:=A.quake k U.mark j (x j) i (hF j).1; have ht:(T i).Tap k (A.read k U.mark j (x j)|>.val i)=0:= hf.2.2.trans ((hF j).2.symm ▸ ((T i).next k U.mark _|>.mp (hh j)).2); apply (Eave.Vita U (i.val+1) i.isLt).1; intro z hz; by_cases h:z=i; · subst z; exact ht
          exact (Eave.Vita U i.val i.isLt.le).2 hf.2.1 z (Nat.lt_of_le_of_ne (by omega) (fun hp=>h (Fin.ext hp)))
       obtain ⟨f,h,h'⟩:= A.skies U hp h i (i.val+1) (Nat.lt_succ_self _) i.isLt x hx hv; let p(j):= x j- f j; have hz(j):(p j).val ∈ A.flag (k+1) j:= (A.depth k j U.mark (p j)).2 (by unfold p;rw [map_sub,(h' j).2,sub_self]); refine ⟨fun j=>⟨(p j).val,hz j⟩, subW A.non hp hx h,fun j=>⟨trims.sub (hF j).1 ((h' j).1.drop (by omega)),?_⟩⟩; change (x j).val i-(f j).val i = _; rw [((hF j).2), (h' j).1 i (by omega),sub_zero]
end Aeon
end YM.OPE.Hark
