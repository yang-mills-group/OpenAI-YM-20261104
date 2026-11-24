import YM.FVAAlt2.Commuting
/-! Bosonic polynomials in the same Taylor-normalized list-slot convention
as the MS kernels. No complex Wick arguments have been fed to real group fields.
Everything is still the arity/formal order data. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Book MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl MS.Cylinder
open Finset
variable {A J:Type}
abbrev pNo (A:Type): Sector A:=fun _=>false
abbrev Bos(A:Type):=Com (pNo A)
namespace Bos
open scoped Classical
local notation "p" => pNo A
local notation "E" => Bos A
local infix:70 " ⋄ " => product p
variable [Fintype A]
set_option linter.unusedSectionVars false

lemma always (F:Raw A ℂ): Koszul.Pure p false F:= by
  have h(w:List A): degree p w=false:= by induction w with| nil=>rfl| cons a w he=> rw [degree_cons,he];rfl
  exact fun l hl=> (hl (h l)).elim

def install (F:Raw A ℂ)(h:Symm p F)(n:ℤ)(hn:Limit F n): E:=⟨F, Com.mem (always F) ⟨h, minH hn⟩⟩

def letter (i:A) : E:= install (atLetter i) (speaks_s _) (1:ℕ) (letterN i)
lemma letter_val (i:A): (letter i).val=atLetter i := rfl

def grad (i:A): E→ₗ[ℂ] E := {
  toFun F:= ⟨D i F.val, Com.mem (always _) ⟨(F.sym).drop i, miD F.small i⟩⟩
  map_add' f g:= Subtype.ext (map_add _ f.val g.val)
  map_smul' _ f:= Subtype.ext (map_smul _ _ f.val) }
lemma grad_v (i:A) (F:E): (grad i F).val = D i F.val := rfl
lemma grad_mul (i:A)(F G:E): grad i (F*G)=grad i F*G+F*grad i G:= by
  apply Subtype.ext; change D i _ = _; rw [Com.mul_val,D_product, show p i=false from rfl,sign_id];rfl
lemma grad_one (i:A): grad i (1:E)=0:= by apply Subtype.ext; rfl
lemma grad_letter [DecidableEq A] (i j:A): grad i (letter j)=if i=j then 1 else 0:= by split; rename_i h; subst i; exact Subtype.ext (hear _); exact Subtype.ext (unheard _ (by assumption))
-- projections onto arity n
lemma mask_symm {F:Raw A ℂ}(h:Symm p F)(n:ℤ): Symm p (mask n F):= by
  intro l i j r; unfold mask; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [show (l++i::j::r).length=(l++j::i::r).length by simp]; split <;> first| exact h l i j r| exact (mul_zero _).symm

def per (n:ℕ): E→ₗ[ℂ] E:={
   toFun F:=install (mask n F.val) (mask_symm F.sym n) n (Limit.mod F.val n)
   map_add' x y:=Subtype.ext (map_add _ x.val y.val)
   map_smul' c x:=Subtype.ext (map_smul _ c x.val) }
lemma per_v (i:ℕ)(F:E): (per i F).val=mask i F.val:= rfl
lemma per_rank(i:ℕ)(F:E): rank i (per i F).val:= rankMod F.val i -- uses rank bind
lemma tally (X:E){n:ℕ}(h:Limit X.val n): (∑ i∈ range (n+1), per i X)=X:= by
  apply Subtype.ext; funext l; rw [Submodule.coe_sum,Finset.sum_apply]; simp_rw [per_v]; by_cases hz: l.length ≤ n; swap; · rw [ Finset.sum_eq_zero, h l (by omega) ]; exact fun i hi=> strange _ (by simp at hi; omega)
  rw [Finset.sum_eq_single_of_mem l.length ( by simp [hz] ), enough l rfl ]; exact fun i _ hi=> strange _ (by omega)
lemma rank0_const (x:E)(hx:rank 0 x.val): x=x.val [] • (1:E):= by
  apply Subtype.ext; rw [Submodule.coe_smul,Com.one_val]; funext l; cases l with
  | nil=> exact (mul_one _).symm
  | cons a l=> rw [hx _ (by rw [mod_int]; simp; omega),Pi.smul_apply]; exact (mul_zero _).symm
lemma radial (x:E) (n:ℕ)(hx:rank n x.val): (n:ℂ) • x=∑ i:A, letter i * grad i x:= by
  let c(i:A):ℂ:=1; apply Subtype.ext; rw [Submodule.coe_smul,Submodule.coe_sum]
  have he (w:List A): Owed c w=(w.length:ℂ):=by induction w with| nil=>simp [Owed]| cons a w ih=>rw [ Owed,List.map_cons,List.sum_cons ]; unfold Owed at ih; rw [ih]; simp only [List.length_cons,Nat.cast_add,c]; ring
  have hv : (n:ℂ) • x.val= Tick c x.val:= by
      funext l; by_cases hl: l.length=n
      · change (n:ℂ)*x.val l=Owed c l * x.val l; rw [he,hl]
      change (n:ℂ)*x.val l=Owed c l*x.val l; simp [hx l (by rw [mod_int]; omega)]
  rw [hv, overture c x.sym]; simp_rw [c,one_smul,Com.mul_val,letter_val,grad_v]

/-- Useful when proving an actual integration rule: coefficient arity induction
by multiplication by a single field leg, without estimating a sum over all degrees. -/
lemma spans (S: Submodule ℂ E)(h: (1:E) ∈ S)(hs:∀ (i:A)(x:E), x∈ S→ letter i*x∈S)(x:E):x∈ S:=by
  obtain ⟨n,hn⟩:= x.small
  suffices hv:∀ k:ℕ,∀ x:E, rank k x.val → x∈ S by rw [← tally x hn]; exact S.sum_mem fun i _=> hv i (per i x) (per_rank i x)
  intro k; induction k with
  | zero=> intro x hx; rw [rank0_const x hx]; exact S.smul_mem _ h
  | succ n ih=>
    intro x hx; rw [← inv_smul_smul₀ (by exact_mod_cast Nat.succ_ne_zero n : ((n+1:ℕ):ℂ)≠0) x, radial x _ hx]; refine S.smul_mem _ (S.sum_mem fun i _=> hs i _ (ih _ ?_)); rw [grad_v]; exact Eq.mp (by simp : rank (n+1-1:ℤ) _= rank (n:ℤ) (D i x.val)) (Rails.enter i hx) -- ↑n+1 synt form
lemma induction (C:E→Prop)(h1:C 1)(hs:∀ a b,C a→C b→ C (a+b))(hv:∀ (r:ℂ) x,C x→C (r•x))(hl:∀ (i:A) x,C x→ C (letter i*x))(x:E): C x:= by
  let s: Submodule ℂ E:={
     carrier:= C
     add_mem' := fun ha hb=> hs _ _ ha hb
     zero_mem':=zero_smul ℂ (1:E) ▸ hv 0 1 h1
     smul_mem':= hv }
  exact spans s h1 hl x
end Bos
end YM.FVAAlt2
