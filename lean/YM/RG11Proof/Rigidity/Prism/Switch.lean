import YM.RG11Proof.Rigidity.Prism.Volume

/-!
# Assembly of joint observables
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Prism
open scoped BigOperators Topology
open Function Set MeasureTheory Metric Submodule
variable {I N : Type} [Fintype I]
local notation "X"=>Desk I
local notation "K"=>circle I
abbrev Track (I N : Type) := N → Desk I → ℝ
def chord (A : Track I N) (l : List N) (x : X) := (l.map fun i=> A i x).prod

def Seen (A B : Track I N) : Prop := ∀ l : List N, (∫ x in K,chord A l x)=∫ x in K,chord B l x

abbrev Fold (I : Type) := (Desk I→ℝ)×(Desk I→ℝ)
-- rolling all tested monomials
def shelf (A B : Track I N) : Submodule ℝ (Fold I) := span ℝ (Set.range fun l=> (chord A l,chord B l))

omit [Fintype I] in
lemma monoids (A B : Track I N) (l : List N) : (chord A l,chord B l) ∈ shelf A B := subset_span (mem_range_self l)
omit [Fintype I] in
lemma symbols (A B : Track I N) (i:N): (A i,B i)∈shelf A B:= by simpa only [show ∀ (A : Track I N),chord A [i]=A i from fun _=>funext fun _=> by simp [chord]] using monoids A B [i]
omit [Fintype I] in
lemma sits_one (A B : Track I N): 1∈shelf A B:= monoids _ _ []
omit [Fintype I] in
lemma chord_cons (A:Track I N) (a : N) (l) (x:X) : chord A (a::l) x=A a x*chord A l x:= by simp [chord]
omit [Fintype I] in
lemma chord_cont (A:Track I N) (h:∀ i,Continuous (A i)) (l : List N) : Continuous (chord A l) := by
  induction l with
  | nil=>exact continuous_const
  | cons a l ih=> rw [funext (chord_cons A a l)]; exact (h _).mul ih

omit [Fintype I] in
lemma sits_product {A B : Track I N} {t u : Fold I} (h : t∈shelf A B)(ht : u∈ shelf A B): t*u ∈ shelf A B:= by
  induction ht using Submodule.span_induction with
  | mem z hz=>
    rcases hz with ⟨L,rfl⟩
    induction h using Submodule.span_induction with
    | mem x hx=> rcases hx with ⟨U,rfl⟩
                 rw [show (chord A U,chord B U)*(chord A L,chord B L)=(chord A (U++L),chord B (U++L)) by ext <;> simp [chord]]
                 exact monoids _ _ _
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy=> rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx=> rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  | zero=>rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy=> rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx=> rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
omit [Fintype I] in
lemma sits_power {A B : Track I N} {t : Fold I} (h : t∈shelf A B)(n:ℕ) : t^n∈shelf A B:= by
  induction n with | zero=> rw [pow_zero]; exact sits_one A B  | succ n ih=> rw [pow_succ]; exact sits_product ih h

lemma seen_on {A B : Track I N} (h : Seen A B) (hA : ∀ i,Continuous (A i))(hB:∀ i,Continuous (B i))
    {t : Fold I} (ht : t ∈ shelf A B) : Continuous t.1 ∧ Continuous t.2 ∧
      (∫ x in K,t.1 x)=∫ x in K,t.2 x := by
  induction ht using Submodule.span_induction with
  | mem v hv=> rcases hv with ⟨l,rfl⟩
               exact ⟨chord_cont A hA l,chord_cont B hB l,h l⟩
  | zero => exact ⟨continuous_const, continuous_const,rfl⟩
  | add u v _ _ hu hv=>
    change Continuous (u.1+v.1) ∧ Continuous (u.2+v.2) ∧ (∫ x in K, u.1 x+v.1 x)=∫ x in K,u.2 x+v.2 x
    refine ⟨hu.1.add hv.1,hu.2.1.add hv.2.1,?_⟩
    have hi (f : X→ℝ)(hf:Continuous f): IntegrableOn f K := hf.continuousOn.integrableOn_compact (isCompact_closedBall ..)
    rw [integral_add (hi _ hu.1) (hi _ hv.1),integral_add (hi _ hu.2.1) (hi _ hv.2.1),hu.2.2,hv.2.2]
  | smul a u _ hu=>
    change Continuous (fun x=> a*u.1 x) ∧ Continuous (fun x=> a*u.2 x) ∧ (∫ x in K, a*u.1 x)=∫ x in K,a*u.2 x
    exact ⟨continuous_const.mul hu.1,continuous_const.mul hu.2.1,by rw [integral_const_mul,hu.2.2,integral_const_mul]⟩
end YM.RG11.Rigidity.Prism
