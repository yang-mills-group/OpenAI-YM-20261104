import YM.FVAAlt2.Winder.Lift
/-! # Commutations for joining KFoot lift calculus. Port use -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind.Lift
open Function Layer Packet Tuple Set Filter Diagram
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y Z W J J' : Type} {r s:ℕ} (e:X ↪ Y)(f:J ↪ J')
abbrev dawn (T:Orders X): Orders Y:= fun i j=> offer e (T i j)
lemma heats (v u: Ranked X)(K:Layer X X)(r:ℕ): offer e (heating K v r)= heating (shore e e K) (fun i=> offer e (v i)) r ∧ offer e (force K v u r)= force (shore e e K) (fun i=> offer e (v i)) (fun i=> offer e (u i)) r:=by
 unfold heating; rw [pushScale,pushSyn,pushLoop]; constructor; rfl
 unfold force; rw [pushSum]; apply Finset.sum_congr rfl; intro z hz; rw [← Finset.mem_antidiagonal.mp hz]; unfold matchTwo; simp only [↓reduceDIte]; rw [pushScale,pushSyn,pushKnot]
lemma drifts (v u:ℕ→ Orders X) (K:Layer X X) (r s i:ℕ): offer e (drift K v u s i r)= drift (shore e e K) (fun w=> dawn e (v w)) (fun w=> dawn e (u w)) s i r:=by unfold drift carry; rw [pushSum]; simp_rw [pushSum]; exact Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=> (heats ..).2 -- insufficient indices?
lemma logd (v:Orders X)(K:Layer X X)(b:Bool)(k:ℕ):dawn e (logHeat K v b k)=logHeat (shore e e K) (dawn e v) b k:=by
 induction k using Nat.strong_induction_on with
 | _ k ih=>
    ext1 i; ext1 r; unfold dawn; cases k
    · rw [logHeat_first,logHeat_first]; split; rw [dark]; rfl
    next k=>
       simp_rw [logHeat_next]; split
       · rw [dark]
       rw [pushScale,pushPlus, pushScale, (heats e (logHeat K v b k i) 0 K r ).1] -- u unused metavariable. simp only?
       rw [drifts, show (fun j=>offer e (logHeat K v b k i j))=(logHeat (shore e e K) (fun i r=> offer e (v i r)) b k i) from congr_fun (ih k (by omega)) i ]; congr 2 -- drifts equal by earlier
       apply congr_arg ((2:ℝ)⁻¹ • ·); exact congr_fun (congr_fun (Diagram.forcing_earlier (K:=shore e e K) k _ _ _ _ (fun m H=> ih m (by omega)) (fun m H=> ih m (by omega))) i) r
lemma pose (v:Orders X)(K:Layer X X)(b:Bool) :dawn e (ceaseHeat K v b)=ceaseHeat (shore e e K) (dawn e v) b:=by
 ext1 i; ext1 r; unfold dawn ceaseHeat heated; rw [pushSum]; exact Finset.sum_congr rfl fun z _=> congr_fun (congr_fun (logd e v K b z) i) r -- ext1 i r ok?
lemma markd (v:ℕ→Orders X)(u:Orders X) (K:Layer X X)(k:ℕ): dawn e (markHeat K v u k)=markHeat (shore e e K) (fun w=> dawn e (v w)) (dawn e u) k:=by
 induction k using Nat.strong_induction_on with
 | _ k ih=>
    cases k
    · rw [markHeat_first,markHeat_first]
    next k=>
       let U:= markHeat K v u; ext1 i; ext1 r; unfold dawn; simp_rw [markHeat_next]; rw [pushScale,pushPlus,(heats e (U k i) 0 K r ).1,drifts, show (fun j=> offer e (markHeat K v u k i j))= _ from congr_fun (ih k (by omega)) i]; congr 2 ; exact congr_fun (congr_fun (Diagram.forcing_earlier (K:=shore e e K) k _ _ _ _ (fun m H=> ih m (by omega)) (fun _ _=>rfl)) i) r
lemma dynamics (v:Orders X)(K:Layer X X)(b:Bool)(u:Orders X)(s:ℕ): dawn e (endHeat s K (logHeat K v b) u)=endHeat s (shore e e K) (logHeat ( shore e e K ) (dawn e v) b ) (dawn e u):=by
 simp_rw [← funext (logd e v K b)]; ext1 i; ext1 r; unfold dawn endHeat heated; rw [pushSum]; exact Finset.sum_congr rfl fun z _=>congr_fun (congr_fun (markd e (logHeat K v b) u K z) i) r
lemma forecast (f:Y↪ J) (v:Packet X r): offer (e.trans f) v=offer f (offer e v):=by
 ext1 x; by_cases h:x∈Set.range (acrossT f)
 · obtain ⟨x,rfl⟩:=h; rw [offer_eq]; by_cases h:x∈ Set.range (acrossT e)
   · obtain ⟨x,rfl⟩:=h; exact (offer_eq _ _ _).trans (offer_eq ..).symm -- defeq maybe stuck
   rw [offer_zero e h, offer_zero]; rintro ⟨y,hx⟩; exact h ⟨y, injectT f hx⟩
 rw [offer_zero f h,offer_zero]; exact fun ⟨y,hy⟩=> h ⟨acrossT e y,hy⟩
local notation "g"=> e.sumMap f
lemma fromFine (v: Packet X r) : offer (e.sumMap f) (offer Function.Embedding.inl v)=offer Function.Embedding.inl (offer e v) := (forecast ..).symm.trans ( forecast e Function.Embedding.inl v ) -- defeq?
lemma rightCrop (v: Packet (X⊕J) r): offer f (crop Function.Embedding.inr v)= Packet.crop Function.Embedding.inr (offer (e.sumMap f) v):=by
 ext1 x; by_cases h:x∈Set.range (acrossT f)
 · obtain ⟨x,rfl⟩:=h; rw [offer_eq]; exact Eq.symm (offer_eq (g) v (Sum.inr∘ x))
 rw [offer_zero f h]; symm; apply offer_zero; intro hh; apply h; rw [here_p]; intro i
 obtain ⟨z,h⟩:=(here_p g _).mp hh i; cases z <;> rename_i z
 · change (Sum.inl (e z):Y⊕ J')= Sum.inr (x i) at h; contradiction
 exact ⟨ z,Sum.inr.inj h ⟩
end YM.RegulatorIR.Budget.FVAAlt2.Wind.Lift
