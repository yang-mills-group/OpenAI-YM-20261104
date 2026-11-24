import YM.MSbar.Fusion.Stator
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Rafts
variable {arn:ℕ}
open Finset Function Marker Extra.Trajectories Accent Entangle Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Ac Extra.Multi Corona
namespace Salt
variable (Z:Salt arn V G n)(w:Name arn V→ℝ)(α η:ℝ)(k M l:ℕ)
def tow (w:Name arn V→ℝ)(α η:ℝ)(k:ℕ)(i:Name arn V):= (η/(arn+1))*w i/ Real.exp (α*k)
lemma towP (hw:∀ i,0<w i)(hp:0<η) i:0<tow w α η k i:= by unfold tow; exact div_pos (mul_pos (div_pos hp (by positivity)) (hw _)) (Real.exp_pos _)
variable (Q:I→ (Aged arn V).Mode)(X:I→Support n)
variable (he:∀ i,(Q i).val.image Z.grain ⊆ X i)(hh:∀ (i:V)(z:Fin (arn+1)),coverNumber M ({Z.focus i,Z.grain (i,z)}:Support n)≤ k)
local notation "S"=> fun i=>Z.kiln (X i) (Q i)
include he hh
lemma attends (i:I): coverNumber M (Z.kiln (X i) (Q i)) ≤ coverNumber M (X i)+ k*(Q i).val.card:=by
   let p:= (Q i).val; let r (q:Finset (Name arn V)):=X i∪ q.image (Z.focus ∘ Prod.fst)
   have hp(t : Finset (Name arn V))(ht:t⊆p): coverNumber M (r t) ≤ coverNumber M (X i) + k*t.card:=by
     induction t using Finset.induction with
     | empty=> simp [r]
     | insert a b hb ih=>
       have ho : Z.grain a∈X i:= he i (mem_image_of_mem _ (ht (mem_insert_self ..))); rcases a with ⟨v,c⟩; specialize ih ((subset_insert _ _).trans ht); rw [Finset.card_insert_of_notMem hb,Nat.mul_add,Nat.mul_one,← Nat.add_assoc]
       have h' : r (insert (v,c) b)= r b∪ {Z.focus v,Z.grain (v,c)}:= by
         ext; simp only [r,mem_union,image_insert,comp_apply,mem_insert,mem_singleton]; grind
       have hl: Z.grain (v,c)∈ r b:=mem_union_left _ ho
       rw [h']; exact (Corona.meets_sum hl (mem_insert_of_mem (mem_singleton_self _)) M).trans (Nat.add_le_add ih (hh v c))
   unfold kiln Entangle.span; rw [image_image]; exact hp _ Finset.Subset.rfl
lemma levels (h:0 ≤ α)(hu:0<η)(hU:η ≤ 1)(hw:∀ i,0<w i)(i:I):
    Real.exp (α*coverNumber M (Z.kiln (X i) (Q i)))*Poly.toll (tow w α η k) (Q i) ≤ (η/(arn+1))^(Q i).val.card * (Real.exp (α*coverNumber M (X i))*Poly.toll w (Q i)):=by
    let z:=Q i; let j:=z.val.card; let H:=Real.exp (α*k); have hx:0<H^j:=pow_pos (Real.exp_pos _) _
    have he := Z.attends k M Q X he hh i
    have hz : Poly.toll (tow w α η k) z=(η/(arn+1))^j*Poly.toll w z/H^j:=by simp only [Poly.toll,tow,prod_div_distrib,prod_mul_distrib,prod_const,div_pow]; rfl
    have hl : Real.exp (α*coverNumber M (Z.kiln (X i) z)) ≤ Real.exp (α*coverNumber M (X i))*H^j := by
       unfold H; rw [← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone; have hi : (coverNumber M (Z.kiln (X i) z):ℝ) ≤ coverNumber M (X i)+ k*j:=by exact_mod_cast he
       nlinarith only [mul_le_mul_of_nonneg_left hi h]
    calc
       _ ≤ (Real.exp (α*coverNumber M (X i))*H^j)*Poly.toll (tow w α η k) z:= mul_le_mul_of_nonneg_right hl (Poly.worth (towP w α η k hw hu) z).le
       _ = _:=by rw [hz]; field_simp; rfl
omit hh
variable [Fintype I]
-- direct neighbor hit by old from roster. no slack in exponent. µ controls focuses only.
local notation "Z₀"=>(arn+1:ℝ)
lemma hitB (h:Occupancy Z.focus l)(F W:I→ℝ)(a g : ℝ)(hx: ∀ i,0 ≤ W i)(hp:0 ≤ a)(hg:0 ≤ g)(hr:Hit X M F α g)(hv:∀ i, W i*Real.exp (α*coverNumber M (Z.kiln (X i) (Q i))) ≤ a*(F i*Real.exp (α*coverNumber M (X i))))(hf:∀ i,(Q i).val.Nonempty → W i*Real.exp (α*coverNumber M (Z.kiln (X i) (Q i))) ≤ a/Z₀*(F i*Real.exp (α*coverNumber M (X i)))) : Hit (fun i=>Z.kiln (X i) (Q i)) M W α ((1+l)*a*g):=by
   intro y; let p:= univ.filter (fun i=> Z.focus i=y)
   let w x i:= if x∈X i then F i*Real.exp (α*coverNumber M (X i)) else 0
   let b i:= a*w y i; let q:=a/Z₀; let C:=p×ˢ(univ:Finset (Fin (arn+1))); let B i:= b i+∑ j∈C,q*w (Z.grain j) i
   have hA j i :0 ≤ w j i:=(hr j).1 i
   have hZ: 0 < (arn+1:ℝ):=by positivity
   have hQ : 0 ≤ q:=div_nonneg hp hZ.le
   have hB i :0 ≤ B i:= add_nonneg (mul_nonneg hp (hA ..)) (sum_nonneg fun _ _=>mul_nonneg hQ (hA ..))
   refine ⟨fun i=> by dsimp only; split; exact mul_nonneg (hx _) (Real.exp_pos _).le; exact le_rfl,Summable.of_finite,?_⟩; rw [tsum_fintype]
   trans ∑ i, B i
   · refine sum_le_sum fun i _=>?_ ; dsimp only; split; swap; exact hB i
     next hu=>
     by_cases hy:y∈X i
     · unfold B b; refine le_trans ?_ (le_add_of_nonneg_right (sum_nonneg fun j _=> mul_nonneg hQ (hA ..))); unfold w; rw [if_pos hy]; exact hv i
     have hL:= (mem_union.mp hu).resolve_left hy; obtain ⟨j,hj,H⟩:=mem_image.mp hL; have hy': j∈p:=mem_filter.mpr ⟨mem_univ _,H⟩; obtain ⟨c,hc⟩:= (spans (Q i) _).mp hj; have hM:= he i (mem_image_of_mem _ hc); have hJ:(j,c)∈C:= mem_product.mpr ⟨hy',mem_univ _⟩
     unfold B; refine (le_trans ?_ (single_le_sum (fun j _=> mul_nonneg hQ (hA (Z.grain j) i)) hJ)).trans (le_add_of_nonneg_left (mul_nonneg hp (hA ..)))
     unfold w; rw [if_pos hM]; exact hf i ⟨(j,c),hc⟩
   unfold B b; rw [sum_add_distrib,sum_comm (f:=fun i j=> q*w (Z.grain j) i)]
   have hc x d (he: (0:ℝ)≤d): ∑ i:I,d*w x i ≤ d*g:=by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Budget.cap (hr x) _) he
   refine (add_le_add (hc y _ hp) (sum_le_sum fun j _=>hc _ _ hQ)).trans ?_
   simp only [sum_const,nsmul_eq_mul]
   have hy: (p.card:ℝ) ≤ l:= by exact_mod_cast h y
   calc
     _ = (1+(p.card:ℝ))*a*g:=by rw [show C.card=p.card*(arn+1) from by simp [C]];unfold q; push_cast; field_simp
     _ ≤ _:= by gcongr
end Salt
end YM.MergeProof.Rafts
