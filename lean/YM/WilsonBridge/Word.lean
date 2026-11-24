import YM.WilsonBridge.Axial
/-!
# Finite word expansion and real substitution in MS polynomials

Keeps the MS factorial/leg convention explicit. The scalar map extended linearly
outside finite-rank for convenience, no value there claimed. Does not use
polynomial density of the **actual** YM measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open Puff.Engine Puff.SplitP Puff.Actors Orbit.LogReal Orbit.Cog Book.Convolve
open Function Finset
open scoped BigOperators Classical
variable {V:Type} [Fintype V] {p:Sector V} {F H G : Raw V ℂ}
local infixl:70 " ⋆ "=> product p

namespace Polynomial
-- submodule induction on monomials of *exact rank*.
def word (p:Sector V): (n:ℕ)→ (Fin n→V) → Raw V ℂ
 | 0, _ => coin 1
 | _+1, f => product p (atLetter (f 0)) (word p _ (f ∘ Fin.succ))
variable (p) (S: Submodule ℂ (Raw V ℂ))
omit [Fintype V] in
lemma word_zero (f:Fin 0 → V): word p 0 f=coin 1:=rfl
omit [Fintype V] in
lemma word_cons {n} (f:Fin (n+1)→ V): word p _ f= atLetter (f 0) ⋆ word p n (f ∘ Fin.succ):=rfl
omit [Fintype V] in
lemma word_rank (n) (f:Fin n→ V) : rank n (word p n f):= by
  induction n with
  | zero => exact Rails.coin _
  | succ n ih => rw [word,show (↑(n+1:ℕ):ℤ)=1+n by omega]; exact (rank_letter (f 0)).product (p:=p) (ih (f ∘ Fin.succ))
omit [Fintype V] in
lemma word_symm (n) (f:Fin n→ V) : MS.Koszul.Symm p (word p n f):= by induction n with| zero =>exact coin_symm _| succ n ih=> exact Symm.times (speaks_s _) (ih (f∘Fin.succ))
lemma combination (n:ℕ)(h:∀ f:Fin n→V,word p n f∈ S)(hr:rank n F)(hs:MS.Koszul.Symm p F) : F∈S:= by
    induction n generalizing F S with
    | zero=>
       have ht (c:ℂ):c • coin (A:=V) (1:ℂ)=coin c:= by funext l; cases l<;>simp [coin]
       rw [rank_zero_eq_coin hr, ← ht (F [])]; exact S.smul_mem _ (h Fin.elim0)
    | succ n ih=>
       rw [expand_rank _ (by omega) hr hs]; apply S.smul_mem
       refine S.sum_mem fun i _=>?_
       refine ih (S.comap (product p (atLetter i))) (fun f=> ?_) (by simpa using hr.enter i) (hs.drop i)
       have hu:= h (Fin.cons i f); rw [word_cons,Fin.cons_zero] at hu; simpa [Function.comp_def] using hu -- comap

-- evaluation in commuting inputs. Rank caps repeated on both sides.
variable (z:V→ℂ)
abbrev chord (z:V→ℂ) : Matrix Unit V ℂ := fun _ => z
abbrev ray (z:V→ℂ) := pull (chord z)
-- coefficient `at t^n` when testing on z times t

def along (z:V→ℂ) (n:ℕ): Linear (Raw V ℂ) ℂ:= (phase n) • ((LinearMap.proj (R:=ℂ) (List.replicate n ())).comp (ray z))
lemma along_read (n:ℕ) : along z n F= phase n * ((ray z) F (List.replicate n ())):=rfl
lemma along_mask {i:ℤ}{n:ℕ} : along z n (mask i F)= if (n:ℤ)=i then along z n F else 0:= by
    simp_rw [along_read,ray,pull_mask]; split_ifs with ht; · rw [enough _ (by simpa using ht)]
    rw [strange _ (by simpa using ht),mul_zero]
lemma along_off {n:ℕ}{r:ℤ}(h:Limit F r)(hv:r<n): along z n F=0:= by
    rw [along_read, show (ray z) F (List.replicate n ())=0 from pull_limit _ h _ (by simpa using hv),mul_zero]
lemma along_piece {n:ℕ}{r:ℤ}(h:rank r F)(hv:r≠ (n:ℤ)): along z n F=0:= by
    rw [ ← (rank_hat r).mp h, along_mask, if_neg (Ne.symm hv) ]

private lemma ray_at (i:V): ray z (atLetter i)= z i • atLetter ():= by
    unfold ray; rw [pull_letter]; simp --
lemma along_letter (i:V) : along z 1 (atLetter i)= z i:= by
    rw [along_read, ray_at, Pi.smul_apply]; change _ * (z i * atLetter () [()])=_; rw [speaks]; simp [Actors.phase]
private lemma per (F:Raw Unit ℂ) (n:ℕ) : product (fun _:Unit=>false) (atLetter ()) F (List.replicate (n+1) ()) = (n+1:ℂ)*F (List.replicate n ()):= by
    induction n generalizing F with
    | zero=> rw [List.replicate_succ]; simp only [List.replicate_zero]; rw [show product _ _ _ _=_ from Based.Position.product_one () (p:=fun _=>false) (atLetter ()) F]; rw [speaks]; simp [atLetter]
    | succ n ih=>
      rw [List.replicate_succ (n:=n+1), D_eval () (product (fun _:Unit=>false) _ _), D_product,hear,coin_product,one_smul, sign_id, Pi.add_apply,ih]
      simp only [at_D,List.replicate_succ,Nat.cast_add,Nat.cast_one]; ring
variable {p} (hz : Tie p (fun _:Unit=>false) (chord z))
local notation "π"=> (fun _:Unit=>false)
include hz
lemma along_cons {i:V}(n) : along z (n+1) (atLetter i ⋆ F) = z i* along z n F := by
   rw [along_read,show ray z _=product π (ray z (atLetter i)) (ray z F) from pull_prod _ hz ..,ray_at,map_smul,LinearMap.smul_apply,Pi.smul_apply,per,Puff.Dynamics.phase',smul_eq_mul,along_read]; field_simp
omit hz

-- useful even where cannot choose well-defined external power counts

def till (z:V→ℂ)(n:ℕ): Linear (Raw V ℂ) ℂ:=∑ j∈ range (n+1),along z j
lemma till_ranked (m:ℕ) (h:rank m F) : till z m F=along z m F := by
   unfold till; rw [LinearMap.sum_apply]; exact Finset.sum_eq_single_of_mem m (by simp) (fun i _ hi=>along_piece z h (by omega))
lemma till_over {n k:ℕ}(h:Limit F n)(ht:n≤k): till z n F=till z k F:= by
    unfold till; simp_rw [LinearMap.sum_apply]; exact Finset.sum_subset (Finset.range_mono (by omega)) (fun i _ hi=> along_off z h (by simp at hi; omega))
lemma backwards (f:Mini V){n:ℕ}(h:Limit f.val n): till z (Swirl.most f) f.val=till z n f.val:= by
    rw [till_over z (c_most f) (le_max_left _ n), till_over z h (le_max_right (Swirl.most f) n)]
def literal (z:V→ℂ): Linear (Mini V) ℂ where
    toFun f:= till z (Swirl.most f) f.val
    map_add' f g:= by
      let n:=max (Swirl.most f) (Swirl.most g); have hf : Limit f.val n:= (c_most f).up (by unfold n; omega); have hg: Limit g.val n:= (c_most g).up (by unfold n; omega); rw [backwards z f hf,backwards z g hg,backwards z (f+g) (hf.add hg : Limit (f+g).val n), Submodule.coe_add,map_add]
    map_smul' c f:= by rw [backwards z (c • f) ((c_most f).smul c : Limit (c • f).val (Swirl.most f)), Submodule.coe_smul,map_smul]; rfl

def value (z:V→ℂ): Linear (Raw V ℂ) ℂ:= (literal z).comp (Mini V).subtype.leftInverse
lemma valuable (n:ℕ) (h: Limit F n): value z F= till z n F:=
    (congr_arg (literal z) (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (Mini V).subtype_injective) (⟨_,minH h⟩:Mini V))).trans (backwards z ⟨_,minH h⟩ h)
lemma at_rank (n:ℕ)(hr:rank n F): value z F=along z n F:= by rw [valuable z n (rank_limit hr), till_ranked z n hr]
lemma at_zero (c:ℂ): value z (coin c)=c:= by rw [at_rank z 0 (Rails.coin c)]; simp [along_read,ray,Actors.phase,coin]
include hz
lemma on_letter {n:ℕ}(i:V)(hr:rank n F): value z (atLetter i ⋆ F)= z i* value z F := by
    rw [at_rank z (n+1) (by rw [show (↑(n+1:ℕ):ℤ)=1+n by omega]; exact (rank_letter _).product hr), along_cons z hz n, ← at_rank z n hr ]
lemma word_value (n:ℕ)(f:Fin n→V): value z (word p n f)=∏ i:Fin n,z (f i):= by
    induction n with| zero=> rw [word_zero,at_zero]; simp| succ n ih=>rw [Fin.prod_univ_succ, word_cons,on_letter z hz (f 0) (word_rank p n (f∘Fin.succ)),ih]; rfl
lemma product_rank (n m:ℕ) (h:rank n F) (hh:rank m H)(hs:MS.Koszul.Symm p F):
    value z (F ⋆ H)=value z F*value z H:= by
    induction n generalizing F with
    | zero=> rw [rank_zero_eq_coin h, at_zero,coin_product,map_smul]; rfl
    | succ n ih=>
        have hx x : rank n (D x F):= by simpa using h.enter x
        rw [expand_rank _ (by omega) h hs, map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply]; simp_rw [map_smul,map_sum,smul_eq_mul,mul_assoc,Finset.sum_mul]; -- issues
        congr 1; refine Finset.sum_congr rfl fun i _=>?_ ; rw [times_assoc,on_letter z hz i (show rank (↑(n+m):ℤ) (((product p) (D i F)) H) from by push_cast; exact (hx _).product hh), on_letter z hz i (hx i),ih (hx i) (hs.drop i), mul_assoc]
lemma value_pair (hf:F∈ FeeP p) (hg:G∈ FeeP p): value z (F ⋆ G)=value z F*value z G:= by
    obtain ⟨pF,n,hn⟩:=fee_spec hf; obtain ⟨pG,m,hm⟩:= fee_spec hg
    rw [limit_eq_rankSum _ hn,limit_eq_rankSum _ hm]
    simp_rw [map_sum,LinearMap.sum_apply]
    simp_rw [map_sum, Finset.mul_sum, Finset.sum_mul, product_rank z hz _ _ (rankMod F (↑_:ℤ)) (rankMod G (↑_:ℤ)) (mask_symm pF)]
end Polynomial
end YM.WilsonBridge
