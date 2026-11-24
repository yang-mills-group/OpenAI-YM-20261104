import YM.MS.Motif.K2
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Warp
/-!
# order two on P∈ Euclid spectrum
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{n:ℕ} {U V:Mield G n}{F H:Rack G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 " ⋄ "=> product S
lemma m_apply (p:Chan G n): Book.rank 1 ( applyS 0 G n p ):= by rcases p with ⟨_|i,s⟩; simp only [applyS,Sc,neg_zero,zero_div,zero_smul, Pi.zero_apply]; exact Rails.zero; simp only [applyS,convoke,zero_smul,add_zero]; exact mon_apply (F:= cwave n G s) (mon_leaf _) _
lemma s2_rank (G:Gauge)(n:ℕ): Book.rank 2 ( ploy G 0 n ):= by
    unfold ploy core; simp only [cur, zero_smul,add_zero]; apply Rails.add; refine Rails.smul _ ?_; exact Rails.sum _ (fun i _=> Rails.sum _ (fun j _=> Rails.sum _ (fun c _=>(rank_α i j c).product (rank_α i j c)))); exact Rails.sum _ (fun i _=> Rails.smul _ ((mon_leaf (onX true i)).product (m_apply i))) -- syntax binder
lemma pairv (h:Book.rank 1 F)(ht:Book.rank 1 H)(i j:Shore G n) : ( F ⋄ H ) [i,j]=F [i]*H [j]+cross (S i) (S j)*F [j]*H [i] := by rw [scattered]; simp only [scatter_cons,scatter_nil,degree_cons,degree_nil,h [] (by simp),h [i,j] (by norm_num),ht [] (by simp),ht [i,j] (by norm_num), Bool.xor_false,cross_false',add_zero,mul_zero,one_mul,zero_add]; ring -- simplify check
lemma core_α (k v:Cfield G n)(p:SectorP n): core G n 0 [(k,-p),(v,p)]= (-(1/4):ℂ) • ∑ a:Arts.L n,∑ b:Arts.L n,∑ i:G.ColorIndex, bite n G (F₀ a b i) (F₀ a b i) [(k,-p),(v,p)] :=by simp only [core,cur,sume,zero_smul,add_zero,Pi.smul_apply,Finset.sum_apply] -- parentheses?
lemma weak_l (k:Cfield G n)(v:Cfield G n)(p:SectorP n)(h:(∀ i a,k≠ at_g i a ) ∨ ( ∀ i a, v≠at_g i a )): core G n 0 [(k,-p),(v,p)]=0:= by
    rw [core_α]; unfold bite; simp_rw [pairv (rank_α _ _ _) (rank_α _ _ _)]; rcases h with he|he <;> simp [ c_α, he ]
-- θ plane only vector evaluate core_μν. reduce color Kronecker
lemma pol_net (a b:Arts.L n)(p:SectorP n): ∑ k:Arts.L n,∑ v:Arts.L n, polar0 k v a p * polar0 k v b p =2*precision a b p:= by
   simp only [polar0,sub_mul,mul_sub,sum_sub_distrib]; -- evaluate four pieces
   simp_rw [Landau.delta]; simp [ite_mul,mul_ite]; unfold precision delta; by_cases h:a=b ; subst b; simp [Momentum.sq,pow_two]; ring; simp [h,Ne.symm h]; ring
end YM.MS.Motif
