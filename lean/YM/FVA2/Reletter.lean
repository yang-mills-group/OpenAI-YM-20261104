import YM.FVA2.Waves
import YM.FVA2.Lag

/-!
# From the input of `PhysicalSum` to full positions and Taylor jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Matrix Function Set Filter Finset Lattice MS MS.Cylinder MS.Koszul MS.Native MS.Native.Wilsonian
open MS.Cylinder.Lab MS.Plane MS.Momentum MS.Book MS.Tone MS.City MS.Orbit MS.Orbit.Cog
open MS.Bare MS.Fleet MS.Swirl MS.Swirl.Near MS.Cylinder.Taylor
open FVA2.Substitute FVA2.Ends FVA2.Lag
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side}
abbrev Words (G:Gauge)(n:Side) := Ends.Alphabet G (Edge (Site n)) (Site n)
local notation "A"=> Words G n
local notation "I"=> FixedMode G n
local notation "ζ"=> Native.Paper G (Site n)
local notation "τ"=> panel G (Site n)

def label (G:Gauge)(n:Side) : Words G n ≃ FixedMode G n where
  toFun
    | Letter.a i=> (Native.Paper G (Site n)).plain ((panel G (Site n)).AId i)
    | Letter.k i=> (Native.Paper G (Site n)).dual ((panel G (Site n)).AId i)
    | Letter.c i=> (Native.Paper G (Site n)).plain ((panel G (Site n)).KId i)
    | Letter.b i=> (Native.Paper G (Site n)).dual ((panel G (Site n)).KId i)
  invFun
    | (((some i,false),v),x) => Letter.a ((x,i),v)
    | (((some i,true),v),x) => Letter.k ((x,i),v)
    | (((none,false),v),x) => Letter.c (x,v)
    | (((none,true),v),x) => Letter.b (x,v)
  left_inv i:= by rcases i with i|i|i|i <;> rfl
  right_inv i:= by rcases i with ⟨⟨⟨_|i,_|_⟩,w⟩,x⟩ <;> rfl
local notation "θ"=> label G n

def indexM : Matrix I A ℝ:= Matrix.of fun i j=> if i=θ j then 1 else 0
abbrev χ (G:Gauge)(n:Side) : Matrix (FixedMode G n) (Words G n) ℂ := intoC indexM
local notation "χ"=> χ G n

lemma index_skin (i:I)(j:A) : χ i j = if i=θ j then 1 else 0 := by unfold Inversion.χ; rw [intoC,map_apply]; unfold indexM; rw [of_apply]; split <;> rfl
lemma index_L {E:Type}[Fintype E](K:Matrix I E ℂ) : χᵀ*K=K.submatrix θ id := by
  ext i j; simp [mul_apply,index_skin,ite_mul]
lemma index_R {E:Type}[Fintype E] (K:Matrix E I ℂ) : K*χ= K.submatrix id θ:= by ext; simp [mul_apply,index_skin,mul_ite]
lemma rightM : χᵀ*χ=1 := by
  rw [index_L]; ext; simp [index_skin, Matrix.one_apply]
lemma leftM : χ*χᵀ=1 := by
  ext i j; rw [mul_apply]; obtain ⟨u,rfl⟩:= (θ).surjective i; obtain ⟨v,rfl⟩:= (θ).surjective j
  rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ u)]; · rw [transpose_apply,index_skin,index_skin,Matrix.one_apply, if_pos rfl,one_mul]; simp only [Equiv.apply_eq_iff_eq]; simp only [(eq_comm : v=u↔ u=v)]
  intro i _ hi; rw [index_skin,if_neg (fun he=> hi ((θ).injective he).symm),zero_mul]
lemma label_compatible (i : A) : σbranch (θ i)=Letter.p i:=by rcases i with _|_|_|_ <;> rfl
lemma circlet : TieField χ σbranch Letter.p := fun i j h=> by by_cases he:i=θ j; rw [he,label_compatible]; exact (h (by simp [index_skin,he])).elim

lemma focused (i:A): ξ[χ] (atLetter (θ i))= atLetter i := by
  rw [variable_form]; simp [index_skin,ite_smul]
lemma stencil_ink (F: FullX G n→ℝ) (h:germ F): ξ[χ] (reads F)= ink tangentVec F := by
  have ht:= ink_change indexM (direction (G:=G) (P:=Site n)) (tangentVec («A»:=Edge _) (P:=Site n)) F (ContinuousLinearMap.id ℝ (FullX G n)) (fun i=>?_) h
  · exact ht
  simp only [indexM,of_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  rcases i with _|_|_|_ <;> rfl

lemma read_action : ξ[χ] (docket n (W G))= (full n).actionBody (priorFull G n) := by
  let u:= glow G (Site n)
  have hv : Native.Chart.loco (Native.Chart.drive n)=(full n).locus (G:=G):= rfl
  have hs(j:Native.Eyes G (Site n)): ξ[χ] ((τ).spark j)= (Letter.focus (Z G (Edge _)) (Z G _)).spark j:= focused (Letter.c j)
  have hk (i : Z G (Edge (Site n))) : ξ[χ] (Focus.stone u ((full n).locus (G:=G)) i)= Focus.stone glowGraph ((full n).locus (G:=G)) i:= by
    unfold Focus.stone; rw [map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [pair_change χ circlet, hs,show ξ[χ] (ink u.e0 (u.seed i∘(full n).locus j))=ink tangentVec _ from stencil_ink (projector i∘ (full n).locus j) ((projector i).contDiff.contDiffAt.comp 0 (smooth_locus _ j))]; rfl
  have hg (j:Native.Eyes G (Site n)) : ξ[χ] (Focus.shadow (τ) (colorTerm G (Site n)) j)= Focus.shadow (Letter.focus (Z G (Edge (Site n))) (Z G (Site n))) (colorTerm G (Site n)) j:= by unfold Focus.shadow; simp_rw [map_sum,map_smul,pair_change χ circlet,hs];
  rw [witnessD, ← prior_full, hv, Focus.Sourced, map_add,
    show ξ[χ] (ink (glow G (Site n)).e0 (priorFull G n))=ink tangentVec (priorFull G n) from stencil_ink _ (prior_full_prop G n).smooth, action_ghost]
  congr 1
  unfold Bonded.hung; rw [(τ).split_i]; simp_rw [map_add,map_sum, map_smul, pair_change χ circlet,
    feeA,feeK,one_smul,neg_smul,one_smul, Finset.sum_neg_distrib,sub_eq_add_neg,
    show ∀ i:Z G (Edge (Site n)),ξ[χ] (atLetter ((ζ).dual ((τ).AId i)))=atLetter (Letter.k i) from fun i=>focused (Letter.k i), show ∀ i: Native.Eyes G (Site n),ξ[χ] (atLetter ((ζ).dual ((τ).KId i)))=atLetter (Letter.b i) from fun i=>focused (Letter.b i), Focus.launch_stone,Focus.launch_shadow ]; -- possibly exact types
  change (∑ i:Z G (Edge _),(product Letter.p (atLetter (Letter.k i))) (ξ[χ] (Focus.stone u ((full n).locus) i))) + -(∑ i:Native.Eyes G _,(product Letter.p (atLetter (Letter.b i))) (ξ[χ] (Focus.shadow _ _ i)))= _
  simp_rw [hk,hg]

lemma read_total : Convolve.promote ξ[χ] (Convolve.promote (docket n) (core G))=
    (full n).total (priorFull G n):= by
  unfold core total; rw [map_add, map_add,
     show Convolve.promote (docket n) (levels 2 (W G))=rankLevel 2 (docket n (W G)) from level_up _ _ _ true,
     show Convolve.promote (docket n) (levels 0 (H G))=rankLevel 0 (docket n (H G)) from level_up _ _ _ true]
  -- α
  funext i; simp_rw [ Pi.add_apply,Convolve.promised, rankLevel, in_rank, read_action, shiftD,show ξ[χ] (ink (glow G (Site n)).e0 Native.Chart.totalH)= HaarBody (Site n) G (Edge (Site n)) from stencil_ink Native.Chart.totalH Native.Chart.nice_totalH ]; -- inspect

end YM.FVA2.Inversion
