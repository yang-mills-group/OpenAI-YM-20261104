import YM.MSbar.Recur.Core
/-! Ready estimates & Mellin pole choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{k n i:ℕ}{d:Bit}{F: ListV C} {z:ℂ}(X: Pulse W)

abbrev L (X:Pulse W) := Work.loop X.pay (d:=0) (show (0:Bit)=0+0 from (by simp))
abbrev T(X:Pulse W) := Work.tree X.pay (d:=0) (e:=0) (show (0:Bit)=0+0+0 from (by simp))
abbrev HPrev (F:ListV C) := ∀ i j, i+j<k+n→ Ready (hood j) W 0 j (F i j) -- abbreviation dangling parameters unused -> turn named
lemma via (h:F 0=0)(H:HPrev (W:=W) (k:=k) (n:=n) F) : Ready (hood n) W 0 n (Score X F k n):=by
    apply Ready.add
    · cases n with
      | zero=> exact Ready.zeroT
      | succ n=> exact Ready.later ((H k n (by omega)).shrinks (deeper (Nat.le_succ n))) (Work.lin _ _) -- shape?
    apply Ready.scale; unfold seek; apply Ready.sum; rintro ⟨a,b⟩ hA; apply Ready.sum; rintro ⟨c,d⟩ hB; dsimp only
    have hu:a+b=k:=Finset.mem_antidiagonal.mp hA; have hv:c+d=n:=Finset.mem_antidiagonal.mp hB
    by_cases he:a=0; rw [he,h,Pi.zero_apply,make_nil]; exact Ready.zeroT
    by_cases hk:b=0; rw [hk,h,Pi.zero_apply,make_rnil]; exact Ready.zeroT
    nth_rw 2 [← hv]; exact Ready.bottled ((H a c (by omega)).shrinks (deeper (show c ≤ n from (by omega)))) ((H b d (by omega)).shrinks (deeper (show d ≤ n from (by omega)))) (Work.poly _ _)
lemma stair (A:ListV C){z:ℂ} : Flat (Score X A k n 0 z):= by
    refine Flat.plus ?_ (Flat.scalar _ ?_)
    · cases n <;> exact Flat.none
    unfold seek; simp_rw [Finset.sum_apply,make,Finset.sum_apply]; refine Flat.sum (fun i _=> Flat.sum fun j _=> Flat.sum fun k _=>?_)
    exact Pale.flat_tree (plug W 0 _).property (plug W 0 _).property (Or.inl X.light)
lemma trunk (X:Pulse W) (U:Set ℂ)(k n i:ℕ): Bright U W 0 (head X k n i):= by unfold head; split_ifs; exact cold (X.calm k); exact Full.zero ..

variable (hv: Ready (hood n) W 0 n (Score X F k n))
include hv
-- uniform pole hit, one increase
lemma stairs : FitsIn (hood n) W 0 (tabs X (Score X F k n) k n) := by
   let q:=Score X F k n; obtain ⟨u,h⟩:= hv.room; refine ⟨1+u,fun i=>?_⟩; unfold tabs; split_ifs with he
   · have hh:Price (1+u) (hood n) W 0 (fun z=> solve (Scale.mass X.law i z) (cap X.law) (q i z)):= ?_ -- underscore
     exact hh.add ((Bright.regular (trunk X (hood n) k n i)).grow (Nat.zero_le _))
     cases i with | zero=>exact (priced (M:=Scale.mass X.law 0) tree_pass (h 0)).grow (by omega) | succ i=> exact priced (true_pass (by omega) he) (h _)
   exact Price.zero
omit hv in
lemma past_end (Y:Film C):(Cap n (tabs X Y k n)) := fun i hi=> by rw [tabs,if_neg (not_le.mpr hi)]
lemma solve_heat (hz:z∈rim (hood n)) (i:ℕ): heat X.law (tabs X (Score X F k n) k n) i z= Score X F k n i z := by
   unfold heat tabs; by_cases hi:i≤n; swap; rw [if_neg hi,hv.cutoff _ (lt_of_not_ge hi),Pi.zero_apply,tick_zero]
   rw [if_pos hi]; let A:=Scale.mass X.law i z; have hu:= clears (M:=X.law) hz.1 hi
   have hf:= hv.lives hz i; have hx:= Inertia.admitted hf hu
   rw [tick_add hx ((trunk X (hood n) k n i).freeze hz.1),reserve hf hu (?_ : tangent _ _)]; swap
   · cases i with
     | zero=> exact Flat.tangent (stair X F) _
     | succ i=> exact fun m x j hh=> ((shifted_out hz hi (by omega) j) hh).elim
   split_ifs with hn
   · obtain ⟨ha,h'⟩:= hn; subst i; simp only [no_add,liftV,(show Scale.tick (fun t=> (X.law t:ℂ)) (X.seed k)=0 by simpa only [no_add] using X.hom k),add_zero]
   simp
lemma coherent : Coherent (hood n) W 0 (scope n) (heat X.law (tabs X (Score X F k n) k n)):= fun i=> Price.recognize (hv.marks i) fun z hz=> by simp_rw [scan,Finset.sum_apply,times,solve_heat X hv hz]
lemma training : Ready (hood n) W 0 n (prepare X F k n):=by
    obtain ⟨i,hi⟩:= stairs X hv; have hK: Cap n (prepare X F k n):= by intro l hl; unfold prepare clean; split_ifs with h; omega; exact past_end X (Score X F k n) _ hl
    refine ⟨hK, ⟨i,fun v=>?_⟩,Coherent.cleans (fun v _ =>hi v) (coherent X hv) (by simp [scope])⟩; by_cases hp:v≤n; exact Coherent.mode (fun t _=>hi t) (coherent X hv) v (by simpa [scope] using hp); rw [hK _ (lt_of_not_ge hp)]; exact Price.zero
lemma spent : ∀ i (z:ℂ), z∈rim (hood n)→ heat X.law (prepare X F k n) i z= Score X F k n i z:= by
   intro i z hz; by_cases he:i≤n; swap; rw [hv.cutoff i (by omega), heat, (training X hv).cutoff i (by omega),Pi.zero_apply, tick_zero]
   obtain ⟨u,H⟩:= stairs X hv; exact Eq.trans (Coherent.flows (fun v hv=> H v) (coherent X hv) i (by simpa [scope] using he) hz) (solve_heat X hv hz i)
omit hv
lemma part : Ready (hood n) W 0 n (evolve X k n):=by
    suffices h:∀ t k n:ℕ,k+n=t → Ready (hood n) W 0 n (evolve X k n) from h _ _ _ rfl
    intro t; induction t using Nat.strong_induction_on with
    | h t ih=> intro k n ht; cases k with
               | zero=> rw [initial,Pi.zero_apply]; exact Ready.zeroT
               | succ i=> rw [grow X (by omega)]; exact training _ (via X (initial X) (fun i j h=> ih (i+j) (by omega) i j rfl))
lemma solve_part : Ready (hood n) W 0 n (Score X (evolve X) k n):= via _ (initial X) (fun i j _=> part ..)
lemma gets (hz:z∈rim (hood n))(i:ℕ): heat X.law (evolve X k n) i z= Score X (evolve X) k n i z:=by
    cases k with
    | zero=> rw [initial]; have he: Score X (evolve X) 0 n=0:= by unfold Score seek; cases n; simp [tripped]; funext v; cases v with | zero=> simp [tripped,Finset.sum_apply,delay] | succ n=> simp [tripped, Finset.sum_apply,delay]
             rw [he,heat]; simp
    | succ i=> rw [grow X (by omega)]; exact spent X (solve_part X) _ _ hz
end YM.MSbar.Play.Produce
