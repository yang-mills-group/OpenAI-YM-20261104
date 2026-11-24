import YM.FVA2.Substitute
import YM.MS.Swirl.Cut

/-!
# Evaluating the bosonic alphabet on actual field values
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bosonic
open Function Set Filter Finset Matrix MS MS.Swirl MS.Book MS.Koszul MS.Puff
open MS.Cylinder MS.Puff.Actors MS.Puff.Mom MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Puff.Dynamics Substitute
open scoped ContDiff Topology Classical
variable {A : Type}

abbrev plain (A:Type) : Sector A := fun _=>false
local infixl:70 " ⋅ " => product (plain A)

variable [Fintype A] {n m:ℕ}

def range_eval (i : ℕ) (x : A → ℂ) : Linear (Raw A ℂ) ℂ :=
  ∑ j∈Finset.range (i+1), Actors.phase j • ((LinearMap.proj (List.replicate j ())) ∘ₗ ξ[Matrix.of (fun a (_:Unit)=> x a)])
lemma range_here (x:A→ℂ)(F:Raw A ℂ) : range_eval n x F = ∑ i∈Finset.range (n+1), Actors.phase i * ξ[Matrix.of fun a (_:Unit)=>x a] F (List.replicate i ()):= by unfold range_eval; rw [LinearMap.sum_apply]; rfl
lemma up {F:Raw A ℂ} (hF : Limit F n)(h:n ≤ m) (x : A→ℂ) : range_eval n x F=range_eval m x F := by
  rw [range_here,range_here]; apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hi hv; rw [limit_change _ _ hF _ (by simp at *; omega),mul_zero]

def base_eval (x:A→ℂ) : (Mini A)→ₗ[ℂ] ℂ where
  toFun f:= range_eval (most f) x f.val
  map_add' f g:= by
    let F:= f+g; let n:= max (most F) (max (most f) (most g))
    rw [up (c_most F) (show _≤n from le_max_left ..),up (c_most f) (show _≤n from Nat.le_trans (le_max_left ..) (le_max_right ..)),up (c_most g) (show _≤n from Nat.le_trans (le_max_right ..) (le_max_right ..))]
    exact map_add _ f.val g.val
  map_smul' c f:= by
    let F:= c • f; let n:=max (most F) (most f)
    rw [up (c_most F) (show _≤n from le_max_left ..), up (c_most f) (show _≤n from le_max_right ..)]
    exact map_smul _ c f.val

def eval (x:A→ℂ) := base_eval x ∘ₗ (Mini A).subtype.leftInverse
lemma evaluating (x:A→ℂ) (F:Raw A ℂ) (hF : Limit F n) : eval x F=range_eval n x F := by
  let f: Mini A:=⟨F,minH hF⟩; have he : eval x F=range_eval (most f) x F := by
    change base_eval x ((Mini A).subtype.leftInverse ((Mini A).subtype f))=_
    rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (Mini A).subtype_injective)]; rfl
  rw [he,up hF (show n ≤ max n (most f) from le_max_left ..),up (show Limit F (most f) from c_most f) (le_max_right n ..)]

lemma value_constant (x:A→ℂ) (c : ℂ) : eval x (coin c)=c := by
  rw [evaluating x _ (coinN c),range_here]; simp [fieldChange,Actors.phase, coin]

lemma raise_one (F:Raw Unit ℂ)(n : ℕ) : product (plain Unit) (atLetter ()) F (List.replicate (n+1) ())=
      (n+1:ℂ)*F (List.replicate n ()) := by
  induction n generalizing F with
  | zero=> rw [List.replicate_succ,D_eval () (product _ _ _), D_product,hear,coin_product,one_smul]; simp [atLetter]
  | succ n ih=> rw [List.replicate_succ (n:=n+1),D_eval () (product _ _ _),D_product,hear,coin_product,one_smul, show (plain Unit ())=false from rfl, sign_id]; rw [Pi.add_apply,ih,at_D,List.replicate_succ]; push_cast; ring

lemma eval_letter_prod (x:A→ℂ) (j:A) (F: Raw A ℂ) (h:F∈Mini _) : eval x (atLetter j ⋅ F)= x j* eval x F := by
  let V:= Matrix.of (fun i (_:Unit)=>x i)
  obtain ⟨n,hn⟩:=h
  rw [evaluating _ _ (n:=n+1) (by push_cast; rw [add_comm]; exact (letterN j).pair hn), evaluating _ _ hn, range_here,range_here]
  have he i : Actors.phase (i+1)* ξ[V] (atLetter j ⋅ F) (List.replicate (i+1) ())= x j * (Actors.phase i * ξ[V] F (List.replicate i ())) := by
    rw [pair_change V (p:=plain A) (q:=plain Unit) (fun _ _ _=>rfl), variable_form, Fintype.sum_unique,
      map_smul, LinearMap.smul_apply, Pi.smul_apply, show (default:Unit)=() from rfl,
      raise_one, Dynamics.phase',smul_eq_mul]
    unfold V; simp only [of_apply]; field_simp [Dynamics.zeroN' i]
  rw [Finset.sum_range_succ'];
  have hv : ξ[V] (atLetter j ⋅ F) []=0:= by rw [field_nil,nil_product]; exact zero_mul _
  rw [show Actors.phase 0*ξ[V] _ _=0 from by rw [List.replicate_zero,hv,mul_zero],add_zero,Finset.mul_sum];
  exact Finset.sum_congr rfl (fun i _=>he i)

lemma homogeneous_split {F:Raw A ℂ}(h:Symm (plain A) F)(hr:Book.rank ((n+1:ℕ):ℤ) F) :
    F=(n+1:ℂ)⁻¹ • ∑ i:A, atLetter i ⋅ D i F := by
  have H := Swirl.overture (fun _:A=>(1:ℂ)) h
  simp_rw [one_smul] at H; rw [← H]; ext l
  change F l=(n+1:ℂ)⁻¹*((l.map fun _=> (1:ℂ)).sum * F l)
  have ht (l:List A) : (l.map fun _=>(1:ℂ)).sum=l.length:=by
    induction l with| nil=>simp|cons i l ih=>simp_all [add_comm]
  rw [ht]; by_cases he:l.length=n+1
  · rw [he]; push_cast; field_simp [zeroN' n]
  rw [hr l (by rw [mod_int]; omega),mul_zero,mul_zero]

lemma spanning (W:Submodule ℂ (Raw A ℂ)) (F:Raw A ℂ) (hf:Symm (plain A) F)
    (hF:F∈ Mini _) (hu:∀ c:ℂ, coin c∈W)
    (hv:∀ (V:Raw A ℂ),Symm (plain A) V→V∈Mini _→V∈W→∀ i:A,atLetter i ⋅ V∈W) : F∈W := by
  obtain ⟨n,hn⟩:= hF
  induction n generalizing F with
  | zero=>
    rw [show F=coin (F []) from funext fun l=>by cases l with | nil=> rfl| cons a l=>exact hn (a::l) (by simp)]
    exact hu _
  | succ n IH=>
    let P:=mask ((n+1:ℕ):ℤ) F
    have ht : Symm (plain A) P:=fun l i j v=> by
      by_cases hp:(l++i::j::v).length=n+1
      · have hh : (l++j::i::v).length=n+1:=by simpa using hp
        unfold P; rw [enough _ (by exact_mod_cast hp),enough _ (by exact_mod_cast hh)]; exact hf ..
      have he:(l++j::i::v).length≠n+1:=by simpa using hp
      unfold P; rw [strange _ (by omega),strange _ (by omega),mul_zero]
    have hP: Limit P ((n+1:ℕ):ℤ):= Limit.mod F _
    have hz : P∈ W := by
      rw [homogeneous_split ht (show Book.rank ((n+1:ℕ):ℤ) P from rankMod _ _)];
      apply W.smul_mem; refine W.sum_mem (fun i _=> ?_); have hh:=ht.drop i; have hl: Limit (D i P) n:= (hP.tip i).up (by omega)
      exact hv _ hh (minH hl) (IH _ hh hl) i
    have H : F-P∈W := by
      apply IH _ (hf.sub ht); intro l hl; rw [Pi.sub_apply]
      by_cases he:(l.length:ℤ)=n+1
      · rw [show P l=F l from enough l (by omega),sub_self]
      rw [hn _ (by omega),hP _ (by omega),sub_zero]
    have hh:=W.add_mem H hz; rwa [sub_add_cancel] at hh

lemma prod_eval (x:A→ℂ) (F H:Raw A ℂ) (he:Symm (plain A) F) (hF:F∈Mini _) (h:H∈Mini _) :
    eval x (F ⋅ H)=eval x F*eval x H:=by
  let P:= eval x ∘ₗ (product (plain A)).flip H
  let M:= eval x H • eval x
  have hP (z:Raw A ℂ): z∈ LinearMap.ker (P-M) ↔ eval x (z ⋅ H)=eval x z*eval x H:= by rw [LinearMap.mem_ker,LinearMap.sub_apply,sub_eq_zero,mul_comm (eval x z)]; rfl
  apply (hP _).mp; refine spanning _ _ he hF (fun c=>?_ ) (fun V _ hx hp i=>?_)
  · apply (hP _).mpr; rw [coin_product,map_smul,value_constant]; rfl
  apply (hP _).mpr; rw [times_assoc,eval_letter_prod x i V hx, eval_letter_prod x i (product _ V H) (miPair hx h), (hP _).mp hp, mul_assoc]
end YM.FVA2.Bosonic
