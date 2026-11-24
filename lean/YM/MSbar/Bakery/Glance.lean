import YM.MSbar.Whisk.Room
import YM.Analysis.SmoothJets
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter Finset Cacao MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {σ ι :Type}[Fintype σ] [DecidableEq σ]
open Lattice MvPolynomial Analysis
local notation "P"=>Pot σ
local notation "V"=>View σ
variable {x y:View σ}{p:Pot σ}{F G : View σ→ℝ}{e: Set (View σ)}{ι' : Type}{q d n:ℕ}

def glance (F:V→ℝ) : List σ → (V→ℝ)
   | []=> F
   | i::L=> glance (D (Pi.single i 1) F) L
lemma glow (L:List σ)(h:ContDiffAt ℝ ((d:ℕ):WithTop ℕ∞) F x)(hp:n+L.length≤d): ContDiffAt ℝ ((n:ℕ): ℕ∞ω) (glance F L) x :=by
   induction L generalizing d F x with
   | nil=> exact h.of_le (Nat.cast_le.mpr hp)
   | cons i L ih=> apply ih (d:=n+L.length) _ le_rfl; refine dSmooth h _ ?_; have ht := (Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hp); push_cast at ht ⊢; simpa [add_assoc] using ht
lemma glance_read (T:List σ) (h:ContDiffAt ℝ ((d:ℕ):WithTop ℕ∞) F x) (he:T.length ≤ d) : glance F T x= iteratedFDeriv ℝ T.length F x (fun i=> Pi.single (T.get i) 1):=by
    induction T generalizing x d F with
    | nil=> exact (iteratedFDeriv_zero_apply _).symm
    | cons i L ih=>
       rw [glance]; have hv : ContDiffAt ℝ (L.length:ℕ∞ω) (D (Pi.single i 1) F) x:= glow [i] h he; rw [ih hv le_rfl]
       have ht:= h.of_le (Nat.cast_le.mpr (show L.length+1≤ d from he)); have hh:=Analysis.cons_inner ht (Pi.single (M:=fun _=> ℝ) i (1:ℝ)) (fun j:Fin L.length=> Pi.single (L.get j) 1); refine hh.symm.trans (congr_arg ((iteratedFDeriv ℝ (L.length+1) F x)) ?_); ext1 a; refine Fin.cases ?_ (fun j=> ?_) a
       · rw [Fin.cons_zero]; rfl
       rw [Fin.cons_succ]; rfl
lemma glance_end (T:List σ)(v:σ): glance F (T++[v])= D (Pi.single v 1) (glance F T):=by induction T generalizing F with |nil=> rfl|cons i T ih=> exact ih
lemma germ (T:List σ) (h:F=ᶠ[𝓝 x] G):glance F T x=glance G T x :=by
    induction T generalizing x F G with
    | nil=>exact h.eq_of_nhds
    | cons i T ih=> exact ih (h.eventuallyEq_nhds.mono fun y hp=> Analysis.GermD (Pi.single i 1) hp)
lemma powerList_eq (K L : List σ) (hp:K.Perm L)(h:ContDiffAt ℝ ((d:ℕ):WithTop ℕ∞) F x)(hv: K.length ≤ d): glance F K x=glance F L x:=by
    induction hp generalizing x F d with
    | nil=> rfl
    | cons i e ih=>
       rename_i a b
       simp only [List.length_cons] at hv
       have h' : ContDiffAt ℝ ((d-1:ℕ):WithTop ℕ∞) (D (Pi.single i 1) F) x:=glow [i] h (by simp; omega)
       apply ih h'; omega
    | swap a b L=>
       -- already symmetry.Mathlib.Fin swap.
       simp only [List.length_cons] at hv; have ht: ContDiffAt ℝ (2: ℕ∞ω) F x := h.of_le (Nat.cast_le (α:=ℕ∞ω) |>.mpr (show 2≤d by omega))
       exact germ L (((ht.eventually (by norm_num)).mono) fun x hh=>Analysis.commuteD hh (Pi.single a 1) (Pi.single b 1))
    | trans hp he p q=> exact (p h hv).trans (q h (hp.length_eq.symm ▸ hv))
lemma TonD (i:σ)(p:Pot σ) : D (Pi.single i 1) (fun z=> eval z p)= fun z=> eval z (pderiv i p):=by
    induction p using MvPolynomial.induction_on with
    | C a=> ext; simp [D]
    | add p q hp hq=>
       ext; rename_i z; have hT(u:P): DifferentiableAt ℝ (fun x'=>eval x' u) z:=(vent u|>.contDiffAt).differentiableAt (by simp); simp_rw [map_add]; conv_lhs => arg 2; skip
       unfold D; rw [fderiv_fun_add (hT p) (hT q)]; exact congr_arg₂ (·+·) (congr_fun hp _) (congr_fun hq _)
    | mul_X p c hp=>
       ext z; simp_rw [pderiv_mul,map_add,map_mul,eval_X]; have h:= (vent p|>.contDiffAt (x:=z)).differentiableAt (by simp); unfold D; let U:View σ→L[ℝ]ℝ:=ContinuousLinearMap.proj c; change fderiv ℝ (fun x:View σ=> eval x p * U x) z (Pi.single i 1)= _; rw [fderiv_fun_mul h U.differentiableAt,U.fderiv]; have he : (MvPolynomial.eval z) ((pderiv i) (X c))=(U (Pi.single i 1)):= by by_cases hx:c=i; subst c;simp [U];rw [pderiv_X_of_ne hx,_root_.map_zero];simp [U,hx]
       rw [he]; have H : D (Pi.single i 1) (fun z => eval z p) z=_:=congr_fun hp z
       rw [← show D (Pi.single i 1) (fun z=> eval z p) z=_ from H]; unfold D; simp [U,mul_comm,add_comm]
lemma glance_jet (p:Pot σ)(T:List σ) : glance (fun z=> eval z p) T x=Whisk.read x T p :=by
    induction T generalizing p with
    | nil=>rfl
    | cons i T ih=> rw [glance,TonD]; exact ih _
lemma blank_list (p:Pot σ)(T:List σ)(hp:p.totalDegree<T.length):Whisk.read x T p=0:=by
   induction T generalizing p with
   | nil=> exact False.elim (Nat.not_lt_zero _ hp)
   | cons i T ih=>
       rw [Whisk.read_next]; by_cases he:p.totalDegree=0
       · conv_lhs => rw [show p=MvPolynomial.C _ from totalDegree_eq_zero_iff_eq_C.mp he, pderiv_C,_root_.map_zero]
       rw [List.length_cons] at hp; apply ih; have hx:=pdeg i (p:=p) (show p.totalDegree ≤ p.totalDegree-1+1 by omega); omega
end YM.MSbar.Bakery
