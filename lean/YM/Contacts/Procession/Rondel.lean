import YM.Contacts.Procession.Torch
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Pulse Pulse.Form Finset Sun
open Milling Milling.Forge Milling.Garf Matrix MvPolynomial
open scoped Topology BigOperators Classical Matrix ContDiff
variable {T α β γ : Type}[AddCommGroup T]{B k i j v p r e:ℕ}
local notation "α†"=>T×α
local notation "β†"=>T×β
local notation "AUX"=>Live T α
section
variable {X Y:Type}
lemma hoist_erase (R:X→Y→ℝ)(i:ℕ): hoist R (0:Pulse.Field (Fin i) X)=0:=by simp [hoist,show allAt (fun _:Fin i=>R) 0=0 from funext fun _=>by simp [allAt]]
lemma cloak_rim (A:House α†) (h: Snug A): Snug (cloak A):= ⟨fun i j=> hoist_shape,fun i j he=>by unfold cloak; rw [h.thin _ _ he, hoist_erase]⟩
lemma bornS (f:Pulse.Field (Fin i) X)(h:Poem f): Proper i (leafS f) := by
    have hh k (h:k≠0): leafS f k=0:= Pi.single_eq_of_ne h _; refine ⟨fun k j=> ?_ , fun k j he=>?_⟩ <;> by_cases ht:k=0
    · subst k; unfold leafS; rw [Pi.single_eq_same]; by_cases hj:j=i; · subst j; simpa
      rw [Pi.single_eq_of_ne hj]; exact Poem.empty
    · rw [hh _ ht]; exact Poem.empty
    · subst k; unfold leafS; rw [Pi.single_eq_same,Pi.single_eq_of_ne (by omega: j≠i)];
    rw [hh _ ht]; rfl
lemma snugs {X Y:House α} (h:Snug X)(ht:Snug Y): Snug (X+Y):= by constructor; intro i j; exact Poem.add (h.poems _ _) (ht.poems _ _); intro i j he; simp only [Pi.add_apply,h.thin _ _ he,ht.thin _ _ he,add_zero]
lemma tagged {A:House α}(h:Proper v A) (hk:v ≤ k+2)(ht:0<k): Snug (shiftA k A):= by -- undecl A
   refine ⟨fun i j=>?_ ,fun i j he=>?_⟩ <;> (unfold shiftA; split)
   exacts [h.sym _ _,Poem.empty,h.thin _ _ (by omega),rfl]
lemma shift_once (b:ℕ)(f:Pulse.Field (Fin i) α): shiftA b (leafS f)=Pi.single b (Pi.single i f):= by
   funext i; unfold shiftA; split
   next h=> unfold leafS; by_cases he:b=i
            · subst b; simp
            rw [Pi.single_eq_of_ne (by omega: i-b≠0), Pi.single_eq_of_ne (Ne.symm he)]
   next h=> rw [Pi.single_eq_of_ne (by omega: i≠b)]
lemma ring_snug {A:House α†}{b:ℕ}(h: Snug A)(hb:0<b)(hp:i+1≤ b+2)(f:Pulse.Field (Fin i) α†): Snug (ringS b f A):= by unfold ringS; rw [← shift_once]; exact snugs (cloak_rim A h) (tagged (bornS _ (print_even (scarab f))) hp hb)
end
-- period clock on finite datum.Mark Hamlet.Measured later after reset.
def planeC {X Y:Type}(U:Matrix X Y ℝ)(F:House X) : House Y:= fun i j=> hoist U (F i j)
def hearth (A:House α†)(G:α†→α†→ℝ)(M: Matrix (T×α) (T×β) ℝ)(f:Pulse.Field (Fin i) α†)(b:ℕ):= planeC (veil M) (massaged (quiet G) (ringS b f A))
lemma hearth_shape {M:Matrix (T×α) (T×β) ℝ}{A:House α†} (h: Snug A)(hb:0<B)(hi:i+1≤ B+2)(G:α†→α†→ℝ)(f:Pulse.Field (Fin i) α†): Snug (hearth A G M f B):= by
    have he:= massaged_shape (g:=quiet G) (ring_snug h hb hi f); refine ⟨fun i j=> hoist_shape,fun i j hu=>by unfold hearth planeC; rw [he.thin _ _ hu,hoist_erase]⟩
variable [Fintype α][Fintype β][Fintype T]
-- weighted comparison at one mark
lemma stamp_add (F H : Sun.St α) : stage i (F+H)=stage i F+stage i H:= by simp only [stage, Pi.add_apply,verse_add, sum_add_distrib]
lemma pin_stage (f:Pulse.Field (Fin i) α) (h:i ≤k+2): stage k (Pi.single i f)=verse f:= by unfold stage; rw [sum_eq_single i,Pi.single_eq_same]; intro j hj he; rw [Pi.single_eq_of_ne he]; exact verse_quiet ..; simp;omega
lemma paid_stage (A:House α†)(F:Pulse.Field (Fin i) α†)(b:ℕ)(h:i+1 ≤b+2)(s:ℝ)(e:ℕ) : castP (core T α) (mote s) (stage e (ringS b F A e))= stage e ((A+shiftA b (leafS (s • F))) e):= by
    unfold ringS; rw [shift_once]; simp_rw [Pi.add_apply,stamp_add,map_add,cast_star]
    by_cases he:e=b; · subst e; rw [Pi.single_eq_same,Pi.single_eq_same,pin_stage _ h, pin_stage (i:=i) (k:=b) _ (by omega),verse_scale']; apply congr_arg; apply MvPolynomial.funext; intro x; change aeval x (castP _ _ _)=aeval x (s • verse _); rw [onePass,map_smul]; exact stem_front .. -- variable subst b? 
    rw [Pi.single_eq_of_ne he _,Pi.single_eq_of_ne he _]; simp [stage,verse_quiet]
lemma gray (M:Matrix α β ℝ)(R:House α)(x:β→ℝ): aeval x (stage i (planeC M R j))= aeval (M *ᵥ x) (stage i (R j)):= by simp_rw [stage,map_sum]; apply sum_congr rfl; intro v _; exact hoist_read M (R j v) _
def rose (A:House α†)(G:α†→α†→ℝ)(R : Matrix (T×α) (T×β) ℝ)(f:Pulse.Field (Fin i) α†):= planeC R (canal G i A (leafS f))
lemma canal_smul_at (A:House α)(G:α→α→ℝ)(s:ℝ)(f:Pulse.Field (Fin i) α): canal G v A (leafS (s • f))=s • canal G v A (leafS f):= by
    have he:A=A:=rfl; have ht: canal G v A 0=0:= by have hx:=canal_linear (A:=A) G (p:=v) 0 0 1; simp only [one_smul,add_zero] at hx; exact (add_left_cancel (show canal G v A 0 + 0= canal G v A 0+canal G v A 0 by rwa [add_zero])).symm
    rw [show leafS (s • f)=s • leafS f+0 from by simp [leafS,Pi.single_smul]]; simpa only [ht,add_zero] using canal_linear G (A:=A) _ 0 s (p:=v)
lemma angles {A:House α†}(G:α†→α†→ℝ)(M : Matrix (T×α) (T×β) ℝ)(f:Pulse.Field (Fin i) α†) (h:Snug A)(hi: i ≤ B)(hv:e < B)(hf:Poem f)(s:ℝ)(x:T×β→ℝ):
      aeval (star s x) (stage (B+e) (hearth A G M f B (B+e)))=aeval (M *ᵥ x) (stage (B+e) (massaged G A (B+e))) + s * aeval x (stage (B+e) (rose A G M f e)):= by
    let k:=B+e; let R:= A+ shiftA B (leafS (s • f)); have ht:Proper i (leafS (s • f)) := bornS _ (hf.scale _); have hh : Snug R:= snugs h (tagged ht (by omega) (by omega));
    rw [hearth, gray,pose,← onePass, (quiet_sc G).ramp (mote s) hh (ring_snug h (by omega) (by omega) _) (fun i _=> paid_stage A f B (by omega) s i)]; rw [bracket G h R ht (by omega) (by omega) (fun j _=> rfl), stamp_add,map_add]; unfold shiftA; rw [if_pos (by omega),Nat.add_sub_cancel_left,canal_smul_at]; unfold rose; rw [gray]; congr 1; simp [stage,verse_scale',mul_sum]
-- coefficient extraction rank with λ-fields exact omission dynamic
open PertExtension.Series House Radial Ion
def porch (A:House (T×α))(G:α†→α†→ℝ)(M:Matrix (T×α) (T×β) ℝ)(f:Pulse.Field (Fin i) α†)(b:ℕ)(e:ℕ): Sun.St (T×β):= fun j=> scoop (hearth A G M f b (b+e) (j+1)) -- want Cover too! Fintype implicit? not used. check
lemma rose_shape {A:House α†} {G:α†→α†→ℝ}{M: Matrix (T×α) (T×β) ℝ}{f:Pulse.Field (Fin i) α†}(h:Snug A)(hf:Poem f) : Proper i (rose A G M f):= by
   have ht:= marsh G h (bornS _ hf); refine ⟨fun i j=> hoist_shape,fun i j hj=>by unfold rose planeC; rw [ht.thin _ _ hj,hoist_erase]⟩
set_option maxHeartbeats 1250000 in
theorem door {A:House α†}(G:α†→α†→ℝ)(M: Matrix (T×α) (T×β) ℝ)(f:Pulse.Field (Fin i) α†)(h:Snug A)(hi:i ≤ B)(hv:e < B)(hf:Poem f): porch A G M f B e = rose A G M f e := by
    let F:= hearth A G M f B; let k:=B+e; let Q:= rose A G M f; let b:=massaged G A k
    let P(n:ℕ):= scoop (F k (n+1)); let W:= Finset.range (k+2); have hx:=hearth_shape (M:=M) h (show 0<B from by omega) (Nat.add_le_add_right hi 1 |>.trans (Nat.le_succ _)) G f; have hq:=rose_shape (A:=A) (G:=G) (M:=M) h hf
    have he(x:β†→ℝ): ∑ j∈W, House.design (P j) x =∑ j∈W, House.design (Q e j) x:= by
       let U:=stage k (F k)
       have hT : aeval (star 0 x) (pderiv (0,none) U) = aeval x (stage k (Q e)):= by
          have hh: (fun a=>aeval (star a x) U)=(fun a:ℝ=> aeval (M *ᵥ x) (stage (B+e) (massaged G A (B+e)))+a* aeval x (stage k (Q e))):= by funext s; exact angles G M f h hi hv hf s x
          refine (slopeP U x).unique (?_); rw [hh]; simpa only [one_mul] using ((hasDerivAt_id' (0:ℝ)).mul_const (aeval x (stage k (Q e)))).const_add (aeval (M *ᵥ x) (stage (B+e) (massaged G A (B+e))))
       have hw j: aeval (star 0 x) (pderiv (0,none) (verse (F k (j+1))))=House.design (P j) x:= nightQ x (show Poem (F k (j+1)) from hx.poems _ _) -- args
       unfold U stage at hT; simp_rw [map_sum] at hT; conv_rhs at hT=> rw [sum_range_succ (n:=k+2)]
       conv_lhs at hT=> rw [sum_range_succ' (n:=k+2)];
       simp_rw [hw] at hT; rw [verse_nil, pderiv_C,map_zero, show Q e (k+2)=0 from hq.thin e (k+2) (by omega), verse_quiet, map_zero, add_zero, add_zero] at hT; exact hT
    let t(i:Sun.St (T×β))(x:β†→ℝ):ℝ:=∑ j∈W,House.design (i j) x
    ext1 j; change P j=Q e j; by_cases hg:j∈ W
    · refine design_eq (poem_scoop (hx.poems _ _)) (hq.sym _ _) (funext fun x=> ?_); have hv(u: Sun.St (T×β)): jet (t u) j x= House.design (u j) x:= by unfold t; rw [loan_sum _ (fun i _=> design_ana ..),Finset.sum_eq_single j]; rw [radiant (design_ana ..) j j (designPower _) x,if_pos rfl]; intro i _ he; rw [radiant (design_ana ..) i j (designPower _) x, if_neg he.symm]; simp [hg]
      have hp:t P=t (Q e):=funext he; rw [← hv,← hv,hp]
    unfold P; simp only [W,Finset.mem_range] at hg; rw [show Q e j=0 from hq.thin e j (by omega), show F k (j+1)=0 from hx.thin k (j+1) (by omega)]; ext1 x; simp [scoop] -- hx.thin is Or infer, zero smul not defeq
end YM.Contacts.Procession.Xenon
