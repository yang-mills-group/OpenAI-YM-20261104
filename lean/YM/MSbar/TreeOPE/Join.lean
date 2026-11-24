import YM.MSbar.TreeOPE.Taylor

/-!
# positions and assembly of mixed Gaussian

Support in conf for rest, cluster, and combined. We do not have to assume
any orbit geometry on the continuum MS side. Could output canonical grade
choice without caring about Euclidean sym of actual scaling limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Set Filter Asymptotics Analysis
open Maxwell Maxwell.Free Maxwell.Wick
open Finsupp Next.Rank.Normal
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {A B : Type} {m n : ℕ} {x : Points n} {y : Points m}

-- concatenate lists, *then* attach the x types.
def combo (x : Points n) (y : Points m): Points (n+m) := points (Fin.append x.ofLp y.ofLp)
def foreign (x : Points n) (y : Points m): Prop := ∀ i j,x i ≠ y j
lemma combination {x : Points n} {y : Points m} (hx:x∈conf n) (hy:y∈conf m) (h:foreign x y): combo x y ∈ conf _:= by
  rintro i j; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> refine Fin.addCases (fun j=>?_) (fun j=>?_) j
  all_goals
    simp only [combo,points_apply, Fin.append_left, Fin.append_right,Fin.castAdd_inj,Fin.natAdd_inj]
  · exact fun he=> (show Injective x.ofLp from hx) he
  · exact False.elim ∘ (h _ _)
  · exact False.elim ∘ (Ne.symm (h _ _))
  exact fun he=>(show Injective y.ofLp from hy) he

abbrev Mark (G : Gauge) (n : ℕ):= Fin n × Slot G
def edges (x : Points n) (y : Points m) (i : Mark G n) (j : Mark G m) := entry i.2 j.2 (x i.1) (y j.1)
private def graft (p : Mark G n ⊕ Mark G m) : Mark G (n+m) := p.elim (fun i=> (Fin.castAdd m i.1,i.2)) (fun i=> (Fin.natAdd n i.1,i.2))
private lemma mark_scope (hx:x∈conf n) (hy:y∈conf m) (h:foreign x y) : scope (fun p=> Finsupp.single (graft p) 1) (frameX (G:=G) (combination hx hy h))= join (frameX hx) (frameX hy) (edges x y):= by
  apply Symmetric.ext; funext i j; simp_rw [match_name graft];
  have ht (i : Fin n) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j:= by
    intro he; have hh:= congr_arg Fin.val he; simp at hh; omega
  cases i <;> cases j <;> simp only [join,graft, frameX, Fin.castAdd_inj,Fin.natAdd_inj, Sum.elim_inl,Sum.elim_inr,if_neg (ht _ _),if_neg (Ne.symm (ht _ _)),combo,points_apply,Fin.append_left,Fin.append_right,edges]
  exact entry_symmetric _ _ (Ne.symm (h _ _))
private lemma combined (p : Fin n→WickPol G) (q: Fin m→WickPol G) :
    (MvPolynomial.rename graft) (front (pot Finset.univ p)*rear (pot Finset.univ q))=pot Finset.univ (Fin.append p q):= by
  unfold pot; simp_rw [map_mul,map_prod]; rw [Fin.prod_univ_add]; simp only [Fin.append_left, Fin.append_right]; congr 1
  · refine Finset.prod_congr rfl fun i _=> ?_
    exact DFunLike.congr_fun (f:= ((MvPolynomial.rename (R:=ℂ) graft).comp front).comp (post i)) (g:= post (Fin.castAdd m i)) (x:=p i) (by ext1 j; simp only [AlgHom.comp_apply,post_X,front,MvPolynomial.rename_X, graft,Sum.elim_inl])
  refine Finset.prod_congr rfl fun i _=> ?_
  exact DFunLike.congr_fun (f:= ((MvPolynomial.rename (R:=ℂ) graft).comp rear).comp (post i)) (g:=post (Fin.natAdd n i)) (x:=q i) (by ext1 j; simp only [AlgHom.comp_apply,post_X,rear,MvPolynomial.rename_X, graft,Sum.elim_inr])

lemma wick_mixed {x : Points n} {y : Points m} (p : Fin n→ WickPol G) (q : Fin m → WickPol G) (hx:x∈conf n) (hy:y∈conf m) (h : foreign x y):
    moment G (combo x y) (Fin.append p q)=mixed (frameX hx) (frameX hy) (edges x y) (pot Finset.univ p) (pot Finset.univ q):= by
  rw [Wick_reads (combination hx hy h)]; change blend _ _ (pot Finset.univ (Fin.append p q))=_; rw [← combined p q,labelled,wets,mark_scope hx hy h, reads_nil]; rfl

def external (y : Points m) (z : E4) (a : Slot G) (b : Mark G m) := entry a b.2 z (y b.1)

def spotX (z : E4): Points 1 := points (fun _=> z)
lemma sole (z : E4): spotX z∈conf 1:= fun _ _ _=> Subsingleton.elim ..
def solo (p : WickPol G) (_i : Fin 1): WickPol G:=p
lemma combined_single {y : Points m} (p : WickPol G) (q : Fin m→WickPol G) (z : E4) (hy:y∈conf m) (h : foreign (spotX z) y) :
    moment G (combo (spotX z) y) (Fin.append (solo p) q)= depend 0 (frameX hy) (external y z) (pot Finset.univ q) p := by
  rw [wick_mixed _ _ (sole z) hy h]; have he : frameX (G:=G) (sole z)=0:= by apply Symmetric.ext; funext i j; exact if_pos (Subsingleton.elim ..)
  rw [he]; unfold pot; rw [Fin.prod_univ_one]; change mixed _ _ _ (post (0:Fin 1) p) _ = mixed 0 (frameX hy) (external y z) p (pot _ q)
  unfold post; rw [labelled, mixed_lift,scope_nil]; rw [show changed (edges (spotX z) y) (fun k : Slot G => Finsupp.single ((0:Fin 1),k) 1) = external y z from ?_]
  · rfl
  funext i j; rw [changed,linearCombination_single,one_smul]; rfl
end YM.MSbar.OPE
