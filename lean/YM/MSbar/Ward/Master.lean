import YM.MSbar.Ward.Base
/-! Anomaly propagation & cancellation at all orders. Doesn't rely on gauge invariant scheme
uniqueness. Only classical balance, free quadratic engine lines & derivative laws here. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce.Shield
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work
open scoped Classical Topology BigOperators
variable {C:Type} {W:Edition C}{X: Pulse W}{k n i:ℕ}{z:ℂ}(A: Shield X)
local notation "LVM" => evolve X
local notation "Φ" => flux A LVM
local notation "Azt" s => (Epoch.grow (propagate (engine A s) true))
local notation "kit" z => pane W 0 LVM z
lemma safe : Ready (hood n) W 1 n (Φ k n):=by
   unfold flux; rw [sub_eq_add_neg,show -(tripped _ _ n)=(-1:ℂ) • _ from (by rw [neg_smul,one_smul])]; refine Ready.add (Ready.add (Ready.spins (part X) (Work.actual _ _)) (Ready.scale ?_ _)) (Ready.scale ?_ _)
   · refine Ready.sum _ fun i hi=> Ready.sum _ fun j hj=> ?_; obtain h:j.1+j.2=n := Finset.mem_antidiagonal.mp hj; nth_rw 2 [← h]; exact Ready.bottled ((part _).shrinks (deeper (show j.1≤n by omega))) ((part _).shrinks (deeper (show j.2≤n by omega))) (Work.poly _ _)
   cases n; exact Ready.zeroT; exact Ready.later ((part _).shrinks (deeper (Nat.le_succ _))) (Work.lin _ _)
lemma at_height (hz:z∈rim (hood n)) : Epoch.elevate (high z X.law 0) (kit z) k n= Calculus.current (Azt z) (kit z) k n := by
    rw [← generator A]; funext i; apply Subtype.ext
    change (high (W:=W) z _ _ ((kit z) k n) i).val= _; rw [wake]; unfold pane shutter; rw [plug_eq ((part _).lives hz i), plug_eq (scored X i z),show Scale.tick _ _= _ from gets (k:=k) X hz i] -- PP loop
-- inheritance from all earlier (smaller rectangle) predictions, robust avoiding lex details
abbrev RimFree (a:ℕ) := ∀ k n, k+n<a → ∀ z∈rim (hood n),∀ i,flux A LVM k n i z=0 -- abbreviation A included?
variable (ht:Dynamic A)
include ht
lemma late (h:RimFree A (k+n))(hz:z∈rim (hood n))(i:ℕ): heat (inc X.law) (Φ k n) i z=0:=by
    let S:=kit z; have hu(j:ℕ)(h:j≤n):z∈rim (hood j):= ⟨deeper h hz.1,hz.2⟩
    have hv(a b)(hw:b≤n)(ho:a+b<k+n): Calculus.anomaly (Azt z) S a b=0 := by
      rw [show Calculus.anomaly (Azt z) S=pane W 1 Φ z from Eq.symm (A.audit LVM z)]; funext i; change plug W 1 _=_; rw [h a b ho z (hu b hw) i]; exact nil
    have he:= Epoch.rigidity (S:=S) (k:=k) (n:=n) (Calculus.next (A.current z) true) (A.progress ht z) (show S 0=0 from (by funext n; unfold S pane; rw [initial]; exact Play.Produce.empty _ _)) (fun i hi j hj=> sub_eq_zero.mpr (at_height A (hu j hj))) (fun i hl=> hv k i (by omega) (by omega)) (fun i hi j hj=> hv i j hj (by omega))
    unfold S at he; rw [← A.audit] at he; apply_fun (fun p:Desk W 1=>(p i).val) at he; rw [wake] at he; change Scale.tick (Scale.mass _ i z) (Deck.plug W 1 _).val=0 at he; rwa [Deck.plug_eq (acts A LVM (k:=k) (n:=n) i z)] at he -- syntax
lemma higher (h:RimFree A (k+n))(hz:z∈rim (hood n))(i:ℕ) (hi: 0 < i): Φ k n i z=0:=by
    by_cases hv: i≤n
    · exact Inertia.hollow (acts A LVM i z) (A.late ht h hz i) (fun m x k hx=> ((Scale.shifted_out hz hv hi k) hx).elim)
    rw [(safe A).cutoff _ (by omega)]; rfl
lemma liberty (h:RimFree A (k+n))(hn:0<n): Φ k n 0=0:= by
    obtain ⟨i,hi⟩:= (Ken.Peak.negc (Nat.ne_of_gt hn)).mp (A.snow k n); apply hi.negative (U:=hood n)
    refine Price.recognize ((safe A (k:=k) (n:=n)).marks 0) (fun z hz=>?_); simp only [scan_zero,Finset.sum_apply]; rw [Finset.sum_eq_single 0]; intro v Hv hV; exact higher A ht h hz v (by omega); simp [scope]
lemma roots_valid (h:RimFree A (k+0)) (hw:z∈rim (hood 0))(hC: Roots A): Φ k 0 0 z=0:= hollow (acts A LVM 0 z) (late A ht h hw 0) ((A.flat hC k).tangent _)
lemma live_e (hA:Roots A) : EqOn (Φ k n i) 0 (rim (hood n)):=by
   have H(t:ℕ) : RimFree A t:= by
      induction t with
      | zero=>intro i k he; omega
      | succ t ih=>
        intro i k ht' z hz j; by_cases he:i+k=t
        swap; exact ih i k (by omega) z hz j
        rcases k with _|k
        · rcases j with _|j; exact roots_valid A ht (by rw [he]; exact ih) hz hA; exact higher A ht (by rw [he];exact ih) hz _ (by omega)
        rcases j with _|j; exact (congr_fun (liberty A ht (k:=i) (n:=k+1) (he ▸ ih) (by omega)) z); exact higher A ht (by rw [he];exact ih) hz _ (by omega)
   exact fun z hz=> H (k+n+1) k n (by omega) z hz i
end YM.MSbar.Play.Produce.Shield
