import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Silo
/-!
# Tree-level identities on the momentum plane

Recover by finite observation. Cubic polarized correctly uses Conserved(F)+Conserved(V) but H any odd or even. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux
variable {R A P I : Type} [CommRing R] [Fintype A] [AddCommGroup P]{p:Sector A}
variable {Z : Charge p P R}{F H V : Row A P R}{K L:Flux A P R}
lemma roll_tree (p:Sector A)(F H:Row A P R)(K:Flux A P R)(i:List (Mode A P)): ∀ᶠ q in atTop,tree p (trim q K) F H i=tree p K F H i:= event_tree (f:=fun _:Finset P=>F) (g:=fun _=>H) (fun _=>by simp) (fun _=>by simp) (fun a b i=>trims i a b) _
lemma pressZ [IsAddTorsionFree R] (h:closed K p false)(hh:closed L p true)(hf:Symm (field p) F)(hp:Pure (field p) false F)(hC:Conserved F)(hv:Symm (field p) V)(hQ:Pure (field p) false V)(hq:Conserved V)(hH:Symm (field p) H):
   tree p L (tree p K F V) H + tree p L F (tree p K V H)+tree p L V (tree p K F H)=tree p K (tree p L F V) H +tree p K F (tree p L V H)+tree p K V (tree p L F H):= by
    ext l
    let s:=atTop (α:= Finset P); have hr (F H V:Row A P R) (K L:Flux A P R): ∀ᶠ i in s, tree p (trim i K) F (tree p (trim i L) H V) l=tree p K F (tree p L H V) l∧ tree p (trim i K) (tree p (trim i L) F H) V l=tree p K (tree p L F H) V l:= by
        exact (event_tree (p:=p) (f:=fun _=>F) (g:=fun i=>tree p (trim i L) H V) (s:=s) (fun _=>by simp) (roll_tree p H V L) (fun a b i=> trims i a b) l).and (event_tree (p:=p) (g:=fun _=>V) (f:=fun i=>tree p (trim i L) F H) (fun _=>roll_tree ..) (fun _=>by simp) (fun a b i=>trims i a b) l)
    obtain ⟨i,⟨h1,h2⟩,⟨h3,Hw⟩,⟨h4,h5⟩,h6,h7⟩:= ((hr F V H L K).and ((hr V F H L K).and ((hr F V H K L).and (hr V F H K L)))).exists
    let W:=field (P:=P) p; let X:=trim i K; let Y:=trim i L
    have he :=Ppress ((cl_trim i h).balanced i) ((cl_trim i hh).balanced i) hp hQ hf hv hH
    simp_rw [← is_loop, ← stickT h i hC, ← stickT hh i hC, ←stickT h i hq, ←stickT hh i hq, ← stickT hh i (conserved_tree _ _ hq F), ← stickT h i (conserved_tree _ _ hq F)] at he;
    simp only [Pi.add_apply]; rw [← h1,← h2,← h3, ← h4,← h5,← h6]; exact congr_fun he l
lemma tree_trans {p:Sector A}(K:Flux A P R) (F:Row A P R) (H:Row A P R): tree p K (translate F) H=tree p K F H:= tree_agrees _ _ _ _ _ (trans_on _)
omit [Fintype A] in
lemma sym_trans (H:Symm (field p) F): Symm (field p) (translate F):= trans_symm F|>.mpr (fun x i j k _=> H x i j k)
omit [Fintype A] in
lemma pure_trans {b:Bool} (H:Pure (field p) b F): Pure (field p) b (translate F) := trans_pure _ _|>.mpr (fun l _=>H l)
lemma q_trans : Agrees (Z.raise (translate F)) (Z.raise F):= Z.agree_at (trans_on _)
-- bring to all-Mom
lemma axis_level (hk:closed K p false)(hx:closed (Z.change K) p true) (H':Symm (field p) H)(h:Pure (field p) false F)(hf: Symm (field p) F): Z.raise (tree p K F H)+tree p (Z.change K) F H = tree p K (Z.raise F) H + tree p K F (Z.raise H):= by
   obtain he := tr_conserve Z (F:=translate F) hk hx (sym_trans hf) (trans_off _) (pure_trans h) H'; simp_rw [tree_trans,tree_agrees K p _ (Z.raise F) _ (q_trans (F:=F))] at he -- FZ
   exact he
lemma axis_press [IsAddTorsionFree R] (h:closed K p false)(hh:closed L p true)(hf:Symm (field p) F)(hp:Pure (field p) false F)(hv:Symm (field p) V)(hQ:Pure (field p) false V)(hH:Symm (field p) H):
   tree p L (tree p K F V) H + tree p L F (tree p K V H)+tree p L V (tree p K F H)=tree p K (tree p L F V) H +tree p K F (tree p L V H)+tree p K V (tree p L F H):= by
   have he := pressZ h hh (sym_trans hf) (pure_trans hp) (trans_off _) (sym_trans hv) (pure_trans hQ) (trans_off _) hH
   have hu : ∀ L K:Flux A P R,tree p L (tree p K (translate F) (translate V)) H= tree p L (tree p K F V) H := fun L K=> tree_agrees _ _ _ _ _ (treesa K F V)
   rw [hu,hu] at he; simpa only [tree_trans] using he -- simp_lint

lemma tree_sym {b:Bool} (h:closed K p b)(hx:Symm (field p) F)(hh:Symm (field p) H): Symm (field p) (tree p K F H):= by
    rw [← tree_trans (F:=F)]; let N l:= roll_tree p (translate F) H K l; intro l i j r; obtain ⟨s,hl,hr⟩:= ((N (l++i::j::r)).and (N (l++j::i::r))).exists; rw [←hl,←hr, stickT (H:=H) h s (trans_off F)]; exact link_symm (slab (trim s K) s) (fun _ h=>slab_sym s h) (sym_trans hx) hh ..
lemma tree_pure {b c d:Bool}(h:closed K p b)(hx:Pure (field p) c F)(hh:Pure (field p) d H): Pure (field p) (c ^^ d ^^ b) (tree p K F H):= by
    rw [← tree_trans (F:=F)]; intro l ht; obtain ⟨s,hs⟩:= (roll_tree p (translate F) H K l).exists; rw [← hs, stickT h s (trans_off F)]; exact link_pure _ (fun c H ht=> (cl_trim s h).pure s ht) (pure_trans hx) hh _ ht
lemma axis_comm {b:Bool}(h:closed K p b)(hf:Pure (field p) false F)(hh:Pure (field p) false H) {l:Legs (Mode A P)}(hw:net l=0): tree p K F H l=tree p K H F l:= by
    rw [← treesa K F H l hw,← treesa K H F l hw]; obtain ⟨s,hs,ht⟩:= ((roll_tree p (translate F) (translate H) K l).and (roll_tree p (translate H) (translate F) K l)).exists; rw [← hs, ← ht,stickT h s (trans_off _), stickT h s (trans_off _),link_commute _ (pure_trans hf) (pure_trans hh)]
lemma axis_even (h:closed K p false)(hf:Pure (field p) false F) {l:Legs (Mode A P)}(hw:net l=0): tree p K H F l=tree p K F H l:= by
    rw [← treesa K F H l hw,← treesa K H F l hw]; obtain ⟨s,hs,ht⟩:= ((roll_tree p (translate F) (translate H) K l).and (roll_tree p (translate H) (translate F) K l)).exists; rw [← hs, ← ht,stickT h s (trans_off _), stickT h s (trans_off _),link_commute_even _ _ (pure_trans hf) ((cl_trim s h).pure s (pure_trans hf))]
end YM.MS.Heat
