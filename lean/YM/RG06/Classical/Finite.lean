import YM.RG06.Classical.Base
import YM.UVExt.FormalThermal
import YM.Work.G05.Taylor
/-!
# Coherence: how many ordinary derivatives of A does a covariant slot read?

Reuse UVExt.EnergyRay.Thermal.JetEq & Work.G05. For kernel of radial
symbol on smooth fields we will only need radialization on *polynomial A*,
since these composition lemmas put every required jet of any smooth
connection exactly in the image of d-th Taylor polynomial, even positive g.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Connection.Jet
open UVExt.EnergyRay.Thermal Function Filter Analysis
open scoped ContDiff Topology

section
variable {E F B J : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
   [NormedAddCommGroup B][NormedSpace ℝ B] [NormedAddCommGroup J][NormedSpace ℝ J]
   {n : ℕ}{x:E}{f f' : E → F}

lemma lower {m:ℕ} (h:JetEq n x f f')(p:m≤n):JetEq m x f f':=
  ⟨h.L.of_le (by exact_mod_cast p),h.R.of_le (by exact_mod_cast p),fun i hi=>h.agree i (hi.trans p)⟩
lemma flip (h:JetEq n x f f'):JetEq n x f' f:=⟨h.R,h.L,fun i hi=>(h.agree i hi).symm⟩
lemma two {g g':E→B}(L:F×B→J)(hp:ContDiff ℝ n L)(h:JetEq n x f f')(u:JetEq n x g g'):
    JetEq n x (fun y=>L (f y,g y)) (fun y=>L (f' y,g' y)):=by
  refine JetEq.chain (f:=fun y:E=>(f y,g y)) (p:=L) ⟨h.L.prodMk u.L,h.R.prodMk u.R,fun i hi=>?_⟩ (JetEq.refl hp.contDiffAt)
  rw [iteratedFDeriv_prodMk h.L u.L,iteratedFDeriv_prodMk h.R u.R,h.agree i hi,u.agree i hi] <;> exact_mod_cast hi
lemma plus {g g':E→F}: JetEq n x f f'→JetEq n x g g'→JetEq n x (fun y=>f y+g y) (fun y=>f' y+g' y):=
  two (fun z:F×F=>z.1+z.2) (contDiff_fst.add contDiff_snd)
lemma less {g g':E→F}: JetEq n x f f'→JetEq n x g g'→JetEq n x (fun y=>f y-g y) (fun y=>f' y-g' y):=
  two (fun z:F×F=>z.1-z.2) (contDiff_fst.sub contDiff_snd)
lemma scale (t:ℝ)(h:JetEq n x f f'):JetEq n x (fun y=>t • f y) (fun y=>t • f' y):=
  h.chain (JetEq.refl (contDiffAt_id.const_smul t))
lemma several {ι:Type*}(l:Finset ι)(a b:ι→E→F)(h:∀ i∈l,JetEq n x (a i) (b i)):JetEq n x (fun y=>∑ i∈l,a i y) (fun y=>∑ i∈l,b i y):=by
  classical
  induction l using Finset.induction_on with
  | empty=> simp; exact JetEq.refl contDiffAt_const
  | @insert i l hi ih=>
    simp only [Finset.sum_insert hi]
    exact plus (h _ (Finset.mem_insert_self ..)) (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma bracket (L:F→L[ℝ] B→L[ℝ] J){g g':E→B}(h:JetEq n x f f')(u:JetEq n x g g'):
    JetEq n x (fun y=>L (f y) (g y)) (fun y=>L (f' y) (g' y)):=
  two (fun z:F×B=>L z.1 z.2) ((L.contDiff.comp contDiff_fst).clm_apply contDiff_snd) h u
lemma slope (v:E)(h:JetEq (n+1) x f f'):JetEq n x (D v f) (D v f'):=by
  have hm : (↑n+1:WithTop ℕ∞) ≤ ↑(n+1:ℕ) := by push_cast; rfl
  refine ⟨dSmooth h.L _ hm,dSmooth h.R _ hm,fun i hi=>?_⟩
  ext1 p
  have hk := lower h (Nat.succ_le_succ hi)
  rw [← cons_inner hk.L,← cons_inner hk.R,hk.agree (i+1) le_rfl]
end

variable {G:Gauge}{n:ℕ}{x:E4}

abbrev Fields (n:ℕ)(x:E4)(A B:Field G):Prop := ∀ i,JetEq n x (A i) (B i)

lemma single_leg {A B:Field G}(i:E4)(h:Fields n x A B):JetEq n x (leg A i) (leg B i):=
   several _ (fun k y=>i k • A k y) (fun k y=> i k • B k y) (fun k _=> scale _ (h k))
lemma shifted (g:ℝ)(k:E4){A B:Field G}{f p:E4→G.Color}(h:Fields n x A B)(u:JetEq (n+1) x f p):
    JetEq n x (shift g A k f) (shift g B k p):=
  plus (slope k u) (scale g (bracket (Lie G) (single_leg _ h) (lower u (Nat.le_succ _))))

/-- m out derivatives of D^l F read A through l+1+m in. -/
theorem slot (g:ℝ)(l:List E4)(i j:E4){A B:Field G}{m:ℕ}(h:Fields (m+l.length+1) x A B) :
    JetEq m x (word g A l i j) (word g B l i j) := by
  induction l generalizing m with
  | nil=>
    have he (u:E4) : JetEq (m+1) x (leg A u) (leg B u):=single_leg _ h
    exact plus (less (slope i (he j)) (slope j (he i))) (scale g (bracket (Lie G) (lower (he i) (Nat.le_succ _)) (lower (he j) (Nat.le_succ _))))
  | cons a b ih=>
    apply shifted
    · exact fun k=>lower (h k) (by omega)
    apply ih; convert h using 2; simp; omega

theorem address_slot (g:ℝ)(s:Address){A B:Field G}(h:Fields (n+s.degree-1) x A B) : JetEq n x (s.read g A) (s.read g B) := by
  apply slot; unfold Address.degree at h; convert h using 2; simp; omega

def ordinaryFrame {G:Gauge}(A:Field G)(n:ℕ) : Field G := fun i=>Work.G05.blockTaylor n (A i)
lemma poly_reads {A:Field G}(h:Regular A 0)(n:ℕ) : Fields n 0 A (ordinaryFrame A n) := by
  intro i
  have ht : ContDiffAt ℝ n (A i) 0:=(h i).of_le (mod_cast le_top)
  exact ⟨ht,(Work.G05.blockTaylor_contDiff n (A i) _).contDiffAt,fun k hk=>(Work.G05.blockTaylor_jets ht k hk).symm⟩
end YM.RG06.Connection.Jet
