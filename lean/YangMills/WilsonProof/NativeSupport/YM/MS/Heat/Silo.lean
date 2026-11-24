import YM.MS.Heat.Silo
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.FiniteMix
import YM.MS.TaylorCharge
/-!
# Extending via observation on finitely many flux points

Proves no-loop identities for the tree calculus even in continuous momentum. Not
 topological convergence of smoothed vertices, just exact recovery of seen values. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux
variable {R A P I : Type} [CommRing R] [Fintype A] [AddCommGroup P]{p:Sector A}
variable {Z : Charge p P R}{F H V : Row A P R}{K L:Flux A P R}
-- moment support. trim all finite rows.
open Classical in
def trim (s:Finset P)(K:Flux A P R): Flux A P R:= fun a b i=> if i∈s then K a b i else 0
omit [Fintype A] [AddCommGroup P] in
lemma needsT {s:Finset P} (i:P)(h:i∉s)(a b): trim s K a b i=0:= if_neg h
omit [Fintype A] [AddCommGroup P] in
lemma trims (i:P)(a b:A): ∀ᶠ s in atTop, trim s K a b i=K a b i:= by classical exact (eventually_ge_atTop ({i}:Finset P)).mono fun s hs=> if_pos (hs (mem_singleton_self i)) -- lint semicolon

lemma trim_charge (s:Finset P): Z.change (trim s K)=trim s (Z.change K):= by
    funext i j z; unfold Charge.change trim; classical
    by_cases h:z∈s <;> simp [h]
omit [Fintype A] [AddCommGroup P] in
lemma cl_trim (s:Finset P){b:Bool}(hk:closed K p b): closed (trim s K) p b:= by
    intro v w t; unfold trim;  by_cases h:t∈s; simp only [if_pos h]; exact hk v w t; simp only [if_neg h]; exact fun h=>(h rfl).elim
omit [AddCommGroup P] in
lemma eventQ {s: Filter I} {f:I→ Row A P R} (h:∀ l, ∀ᶠ u in s,f u l=F l) : ∀ w,∀ᶠ u in s, Z.raise (f u) w=Z.raise F w:= by
   -- visit lemma
   have he (b)(p:Sector A)(w:Legs (Mode A P))(U:I→Slash A P R) (V:Slash A P R)(h:∀ l i r, l++i::r=w→ ∀ᶠ u in s,U u l i r=V l i r): ∀ᶠ u in s, visit b p w (U u)=visit b p w V:= by
       induction w generalizing U V with| nil=> simp [visit]| cons i w ih=> simp_rw [visit_cons]; filter_upwards [h [] i w rfl, ih (fun u z j t=> U u (i::z) j t) (fun z j t=>V (i::z) j t) (fun l j t he=> h (i::l) j t (by simp [he]))] with v hv hx; rw [hv,hx]
   intro w; simp_rw [visit_Z]; refine he _ _ _ _ _ (fun l i r he=> ?_); filter_upwards [eventually_all.mpr (fun a:A=> h (l++(a,i.2)::r))] with v hv; simp_rw [hv]
lemma finadd {A R:Type}[AddCommMonoid R] {s: Filter I}(l:Finset A)(U:I→ A→R)(V:A→R)(H:∀ i∈l,∀ᶠ u in s,U u i=V i): ∀ᶠ u in s, ∑ i∈l,U u i=∑ i∈l,V i:= ((l.eventually_all).mpr H).mono fun _ h=> Finset.sum_congr rfl h
-- issue universe I
lemma event_tree {s:Filter I} {f g:I→ Row A P R}{U:I→ Flux A P R}(h:∀ a, ∀ᶠ i in s, f i a=F a)(hH:∀ a,∀ᶠ i in s,g i a=H a)(hk:∀ a b p,∀ᶠ i in s, U i a b p= K a b p) (w:Legs (Mode A P)): ∀ᶠ i in s, tree p (U i) (f i) (g i) w=tree p K F H w:= by
   unfold tree; refine gathers w _ _ _ (fun l i hi=>?_); unfold attaches; dsimp only; refine finadd _ _ _ (fun a _=> finadd _ _ _ (fun j _=> ?_));
   filter_upwards [hk a j (-net l),hk a j (- -net l),h ((a,-net l)::l),h ((j,-net l)::l),hH ((j,- -net l)::i),hH ((a,- -net l)::i)] with y h1 h2 h3 h4 h5 h6; rw [h1,h2,h3,h4,h5,h6]

variable (Z)
lemma stickT {b:Bool} (h:closed K p b) (u:Finset P) (hw:Conserved F): tree p (trim u K) F H = link (slab (trim u K) u) b (field p) F H :=(localize (cl_trim u h) u (fun i hi a b=> needsT i hi a b) hw H).symm
-- translation setting helpers
lemma tree_agrees (K:Flux A P R)(p:Sector A)(F H V:Row A P R)(h:Agrees F H): tree p K F V=tree p K H V:= by
   funext i; apply scatter_congr _ i; intro a b hq; unfold attaches; simp only; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro t _; rw [h _ (by simp),h _ (by simp)]
lemma treesa {p:Sector A} (K:Flux A P R) (F H:Row A P R): Agrees (tree p K (translate F) (translate H)) (tree p K F H):= agrees_tree _ _ K p (trans_on _) (trans_on _) -- tt
-- no charge² anomaly
lemma tr_conserve (hk:closed K p false)(hx:closed (Z.change K) p true) (hS:Symm (field p) F)(hC:Conserved F)(h:Pure (field p) false F) (he:Symm (field p) H): Z.raise (tree p K F H)+tree p (Z.change K) F H=tree p K (Z.raise F) H+tree p K F (Z.raise H):= by
    ext l; let w := atTop (α:=Finset P)
    obtain HH := (eventQ (Z:=Z) (event_tree (F:=F) (p:=p) (H:=H) (fun i=> Eventually.of_forall (fun _:Finset P=> (rfl:F i=F i))) (fun i=> Eventually.of_forall (fun _:Finset P=> (rfl:H i=H i))) (fun a b i=> trims (K:=K) i a b)) l)
    have hm (F H:Row A P R)(K:Flux A P R): ∀ᶠ i in w,tree p (trim i K) F H l=tree p K F H l:= event_tree (f:=fun _=>F) (g:=fun _=>H) (fun i=> by simp) (fun i=> by simp) (fun a b i=> trims i a b) _
    obtain ⟨i,h1,h2,h3,h4⟩:= (HH.and ((hm F H (Z.change K)).and ((hm (Z.raise F) H K).and (hm F (Z.raise H) K)))).exists
    rw [Pi.add_apply,Pi.add_apply,← h1,← h2,← h3,← h4, stickT hk i hC,stickT hx i hC,stickT hk i (Z.conserve F hC),stickT hk i hC,← trim_charge]
    refine congr_fun (charge_arc (T:=Z.move) (fun f hf=> Charge.exchange Z (trim i K) (cl_trim i hk) i) hS he h ((cl_trim i hk).pure i h)) l
end YM.MS.Heat
