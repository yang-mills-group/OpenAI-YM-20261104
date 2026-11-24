import YM.RG02.Laurent.Foundation

/-! L1 algebra. Products on slots assembled ABSOLUTELY, no
suppressed justification even when changing from periodic sums to Laurent
spells. Having through-order finite, of course use analytic input widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Laurent
open Function Equiv Finset Lattice
open scoped Classical BigOperators
variable {B V : Type}
variable {R : Type}[NormedCommRing R][CompleteSpace R]

private lemma crossFin (n:ℕ) {X : Fin n → Type}(f : ∀ i,X i→R) (h : ∀ i,Summable fun a:X i=>‖f i a‖) :
    Summable (fun g: ∀ i:Fin n,X i=> ‖∏ i:Fin n,f i (g i)‖) ∧
    HasSum (fun g: ∀ i:Fin n,X i=> ∏ i:Fin n,f i (g i)) (∏ i:Fin n,∑' a:X i,f i a):=by
    induction n with
    | zero => refine ⟨.of_finite,?_⟩; convert hasSum_fintype (fun g: ∀ i:Fin 0,X i=> ∏ i:Fin 0,f i (g i)) using 1; simp
    | succ k ih =>
      let F := Fin.consEquiv X
      obtain ⟨hT,hU⟩:=ih (X:=fun i=> X i.succ) (fun i=>f i.succ) (fun i=> h _)
      let g (t:∀ i:Fin (k+1),X i):=∏ i:Fin (k+1),f i (t i)
      have hg (t) : g (F t)= f 0 t.1 * ∏ i:Fin k,f i.succ (t.2 i):=by simp [g, Fin.prod_univ_succ,F]
      constructor
      · apply F.summable_iff.mp
        change Summable ((fun t=> ‖g t‖) ∘ _)
        apply Summable.congr ((h 0).mul_norm hT); exact fun i=>congr_arg norm (hg i).symm
      change HasSum g _
      rw [← F.hasSum_iff, Fin.prod_univ_succ]
      exact (((h 0).of_norm.hasSum).mul hU ((h 0).mul_norm hT).of_norm).congr_fun (fun i=>hg i)

/-- Any finite V, index arbitrary. -/
theorem cross [Fintype V] {X : V → Type}(f : ∀ i,X i→R) (h : ∀ i,Summable fun a:X i=>‖f i a‖) :
    Summable (fun g: ∀ i:V,X i=> ‖∏ i:V,f i (g i)‖) ∧
    HasSum (fun g: ∀ i:V,X i=> ∏ i:V,f i (g i)) (∏ i:V,∑' a:X i,f i a):=by
    let k:= Fintype.card V; let e:Fin k≃V:= (Fintype.equivFin V).symm; let E:= Equiv.piCongrLeft X e
    obtain ⟨hf,hF⟩:= crossFin (R:=R) k (X:=fun i=> X (e i)) (fun i=> f (e i)) (fun i=> h _)
    let g (t:∀ i:V,X i) := ∏ i:V,f i (t i)
    have he (x) : (∏ i:Fin k,f (e i) (x i))= (g ∘ E) x:= Fintype.prod_equiv e _ _ (by intro i; dsimp [E]; rw [Equiv.piCongrLeft_apply_apply])
    constructor
    · apply E.summable_iff.mp
      exact hf.congr fun x=> congr_arg norm (he x)
    rw [← e.prod_comp (fun i=>∑' j,f i j)]
    apply E.hasSum_iff.mp
    exact hF.congr_fun fun i=>(he i).symm

namespace Ringlet
variable {L:Ringlet V B}
abbrev LineSet (L:Ringlet V B):= ∀ i:V,L.Relative Cover i→ℂ
abbrev Row (L:Ringlet V B) := ∀ i:V,L.Relative Cover i
-- don't assume rate positive until comparison

def volume (a:ℝ)(i:V)(g:L.Relative Cover i→ ℂ)(u:L.Relative Cover i) := Real.exp (a*L.bulk i u) * ‖g u‖
def Earn (a:ℝ)(i:V)(g:L.Relative Cover i→ℂ) := ∑' u:L.Relative Cover i, volume a i g u
def Nimble (a:ℝ)(f : L.LineSet) := ∀ i,Summable (volume a i (f i))

variable {a:ℝ}{f:L.LineSet}
lemma Nimble.slim (he : Nimble a f){d:ℝ}(h:d≤a) : Nimble d f:=by
    intro i; apply Summable.of_nonneg_of_le ?_ ?_ (he i)
    · intro j; exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    intro j; unfold volume; gcongr

lemma Nimble.summable (he : Nimble a f)(h : 0 ≤ a)(i:V) : Summable fun u:L.Relative Cover i=>‖f i u‖:= by exact (he.slim h i).congr (fun j=> by simp [volume])
variable [Fintype V]

def Stipend (a:ℝ)(f:L.LineSet) := ∏ i:V,Earn a i (f i)
def rate (f:L.LineSet)(u:L.Row) := ∏ i:V,f i (u i)

lemma absolute_production (he : Nimble a f) :
    HasSum (fun u:L.Row=> Real.exp (a*Fuel u) * ‖rate f u‖) (Stipend a f):=by
    apply (cross (fun i=> volume a i (f i)) (fun i=> (he i).norm)).2.congr_fun
    intro i; unfold Fuel; rw [Nat.cast_sum,Finset.mul_sum,Real.exp_sum,rate,norm_prod,← Finset.prod_mul_distrib]; rfl
lemma principal (he : Nimble a f)(h : 0≤a) : Summable fun u:L.Row=> ‖rate f u‖ :=by simpa only [zero_mul,Real.exp_zero,one_mul] using (absolute_production (he.slim h)).summable

variable (L)
def tint (n:Side)(i:V)(u:L.Relative Cover i) : L.Relative (Site n) i:= ⟨fun j=> wrap n (u.val j), by dsimp only; rw [u.property,map_zero]⟩
omit [Fintype V] in
@[simp] lemma cast_tint (n:Side)(u:L.Row)(i:V): L.castAll (wrap n) u i = tint L n i (u i):= rfl

variable {L}
-- canonical periodized translation-invariant inputs (integrand-level). -/
def receive (f:L.LineSet) (n:Side)(i:V)(v:L.Relative (Site n) i) := ∑' u:L.Relative Cover i, if L.tint n i u=v then f i u else 0
-- torus integrand weight

def tor (f:L.LineSet)(n:Side)(x:B→Site n) := ∏ i:V, receive f n i (L.slice x i)

lemma periodic (he : Nimble a f) (h : 0 ≤ a) (n:Side)(x:B→Site n) :
    HasSum (fun u:L.Row => if L.slice x=L.castAll (wrap n) u then rate f u else 0) (tor f n x):=by
    let g(i:V)(t:L.Relative Cover i):ℂ:= if L.tint n i t=L.slice x i then f i t else 0
    have hg (i:V) : Summable (fun u=> ‖g i u‖):= by
       apply Summable.of_nonneg_of_le (fun k=> norm_nonneg _) _ (he.summable h i); intro k; unfold g; split <;> simp
    change HasSum _ (∏ i:V,∑' u:L.Relative Cover i,g i u)
    apply (cross g hg).2.congr_fun
    intro u; split
    · next hh=> symm; apply prod_congr rfl; intro i _; unfold g; rw [← cast_tint,← hh, if_pos rfl]
    rename_i hh; rw [funext_iff] at hh; push Not at hh; obtain ⟨i,hi⟩:=hh; symm; exact prod_eq_zero (mem_univ i) (if_neg (Ne.symm hi))

end Ringlet
end YM.RG02.Laurent
