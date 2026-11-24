import YM.FVA2.Lag
import YM.FVA2.TreeSelect

/-!
# The rooted Wick operator on a tree slice.

Kill A on tree, K off tree, B everywhere. After this *linear* restriction, the
interacting vertices (from unmarked Body) and Faddeev-Popov *interaction* have
only A slots. The free FP operator is not simply dropped from a field-dependent
measure by fiat. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion.Choice
open Finset Matrix Function Set Filter Lattice MS MS.Native MS.Koszul MS.Bare MS.Book MS.Book.Convolve
open MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Puff MS.Puff.Actors
open MS.Cylinder MS.Cylinder.Taylor Ends ArrayMap Lag Substitute Letter
open scoped Topology ContDiff Classical
open PertExtension Orb

variable {G:Gauge}{n:Side}(T : Choice G n)
local notation "Rt"=> root n
local notation "v"=> T.includeCo
local notation "w"=> T.takeTree
abbrev allLetters (G:Gauge)(n:Side) := Ends.Alphabet G (OEdge n) (Vert n)
local notation "φ"=> allLetters G n

def projectChart : Matrix φ φ ℝ:= moveL (v*vᵀ) (wᵀ*w) 1 0
local notation "ξt"=> ξ[intoC T.projectChart]
lemma paysT : Tie p p (intoC T.projectChart)ᵀ := by unfold projectChart; rw [alignL]; exact preserves_p _ _ _ _
local notation "ΣΣ" => grain (intoC T.Ctilt) (intoC T.fix)

abbrev target (G:Gauge)(n:Side) := priorRoot G n

theorem view_P {F : Raw φ ℂ}(h:F ∈ Mini _): View ΣΣ (ξt F) = View ΣΣ F := by
  rw [view_change (K:= (show Matrix _ _ ℂ from ΣΣ)) _ _ h]
  apply congr_arg (fun U:Grain φ=> View U F)
  have he : w*wᵀ=1:= by unfold takeTree; rw [show (coordinate (pick (G:=G) T.tree))ᵀ=_ from (congr_arg transpose (extend_matrix T.tree G)).symm.trans (transpose_transpose _), ← coordinate_mul,pickedL,coordinate_id]
  rw [projectChart, alignL, commute_grain]; congr! 1
  -- A/A
  · rw [← into_transpose,← into_mul,← into_mul]; congr 1
    unfold Ctilt; rw [transpose_mul, transpose_transpose];
    have hx : v*vᵀ*v=v := by rw [Matrix.mul_assoc,T.co_inv,Matrix.mul_one]
    calc
      _ = (v*vᵀ*v)* T.inverseCo * (v*vᵀ*v)ᵀ:= by rw [transpose_mul,transpose_mul,transpose_transpose]; simp only [Matrix.mul_assoc]
      _ = _:= by rw [hx]
  rw [← into_transpose, into_one,Matrix.one_mul,← into_mul]; congr 1
  rw [transpose_mul, transpose_transpose];
  calc
    _ = T.param * ((w * wᵀ)*w) := by unfold fix; rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = _ := by rw [he,Matrix.one_mul]

def tree_slice : RootX G n→ₗ[ℝ] RootX G n:= extend_zero (fun i=>¬T.tree i) G ∘ₗ pick (fun i=>¬T.tree i)
def cut : RootX G n→L[ℝ] RootX G n := T.tree_slice.toContinuousLinearMap
lemma cut_M : coordinate T.cut.toLinearMap=v*vᵀ := by change coordinate (_ ∘ₗ _) = _; rw [coordinate_mul,T.co_T]

lemma cut_ink (F:RootX G n→ℝ)(hf:germ F) : ξt (ink tangentVec F)=ink tangentVec (F ∘ T.cut) := by
  unfold projectChart; rw [← cut_M]; exact kin_change _ _ _ _ _ hf

lemma projection_off (x:RootX G n) (i:OEdge n)(h:T.tree i) : T.cut x i=0:= by simp [cut,tree_slice,extend_zero,h]

lemma not_k (x: Z G (OEdge n))(h:¬T.tree x.1): ξt (atLetter (Letter.k x))=0 := by
  unfold projectChart; rw [alignL,slotK]
  have hz (i:Z G {i//T.tree i}): w i x=0 := by
    unfold takeTree; rw [pick_matrix, if_neg]; intro he
    apply h; rw [← he]; exact i.1.property
  simp_rw [intoC, Matrix.map_apply,Matrix.mul_apply,Matrix.transpose_apply,hz,zero_mul,
    sum_const_zero,Complex.ofReal_zero,zero_smul,sum_const_zero]
lemma c_unchanged (x:Z G (Vert n)): ξt (atLetter (Letter.c x))=atLetter (Letter.c x) := by unfold projectChart; rw [alignL,slotC,into_one]; simp [Matrix.one_apply,ite_smul]
lemma b_removed (x:Z G (Vert n)): ξt (atLetter (Letter.b x))=0 := by
  unfold projectChart; rw [alignL,slotB,into_zero]; simp

lemma cost_after (r : ℕ)(hr:0<r) :
    rankLevel 2 (ξt ((root n).actionBody (target G n))) r = rankLevel 2 (ink tangentVec ((target G n) ∘ T.cut)) r := by
  let Y:= glowGraph (A:= OEdge n) (P:=Vert n) (G:=G)
  let K:Raw φ ℂ →ₗ[ℂ] Raw _ ℂ:= ξt
  let F:=focus (Z G (OEdge n)) (Z G (Vert n)); let X:= (root n).locus (G:=G)
  have he (i : Z G (OEdge n))(hi : T.tree i.1) :
      K (Focus.stone Y X i)=∑ t:Z G (Vert n),
        product p (atLetter (Letter.c t)) (coin ((projector i (X t 0):ℝ) : ℂ)) := by
    rw [show Focus.stone Y _ _= _ from Ends.stone_terms ..,map_sum]; refine Finset.sum_congr rfl fun j _=>?_
    unfold K; rw [pair_change _ T.paysT,c_unchanged,cut_ink]; swap; · exact (Ends.vibes _).vectorSeed Y i j
    congr 1
    rw [show (projector i ∘ (root n).locus j) ∘ T.cut= (fun _=>projector i (X j 0)) from ?_] -- parentheses
    · exact ink_const ..
    funext y; dsimp only [Function.comp_apply]; simp_rw [Native.projector_k]; unfold X; rw [Ends.locus_at,Ends.locus_at, T.projection_off _ i.1 hi]; rfl
  rw [action_ghost,map_add,cut_ink T _ (prior_root_prop ..).smooth]
  unfold rankLevel; rw [map_add,map_sub,map_sub,map_sum, map_sum,map_sum,map_sum]
  have hQ (i: Z G (OEdge n)) : mask (r+2:ℤ) (K (product p (atLetter (Letter.k i)) (Focus.stone Y X i)))=0 := by
    by_cases hz : T.tree i.1; swap
    · unfold K; rw [pair_change _ T.paysT, T.not_k _ hz,map_zero,LinearMap.zero_apply,map_zero]
    have hr (i : Z G (Vert n)) (x:ℂ) : product p (atLetter (Letter.c i : φ)) (coin x)=x • atLetter (Letter.c i):= by rw [← Pure.central (coin_pure _),coin_product]
    rw [show K (product p _ (Focus.stone Y X _))= _ from pair_change _ T.paysT _ _,he i hz]
    simp_rw [hr]
    funext z; by_cases hp:(z.length:ℤ)=r+2; swap; · exact strange _ hp
    rw [enough z hp]; exact Limit.pair (limit_change _ _ (letterN _)) (Limit.sum _ (fun i _=> Limit.smul _ (letterN (Letter.c i)))) z (by omega)
  have hw (i: Z G (Vert n))(v':Raw φ ℂ) : ξt (product p (atLetter (Letter.b i)) v')=0:= by
    rw [pair_change _ T.paysT,b_removed,map_zero,LinearMap.zero_apply]
  change _+ ((∑ i:Z G (OEdge n),mask (r+2:ℤ) (K (product p (atLetter (Letter.k i)) (Focus.stone Y X i))))-(∑ i:Z G (Vert n), _))= _
  simp_rw [hQ,hw,map_zero,sum_const_zero,sub_zero,add_zero]

abbrev CO := Z G T.Co
/-- Move from an interaction already expressed on the physical slice to
A-only slots of the full Wick evaluation. -/
def appear : Matrix T.CO φ ℝ
| i, Letter.a j => T.takeCo i j
| _, _ => 0
local notation "TT" => ξ[intoC T.appear]
def bring : RootX G n→L[ℝ] (Ends.Links G T.Co) := (pick (fun x=>¬T.tree x) (G:=G)).toContinuousLinearMap
def send_A : Ends.Links G T.Co →L[ℝ] RootX G n:= (extend_zero (fun i=>¬T.tree i) G).toContinuousLinearMap
abbrev coInk (F : RootX G n→ℝ) := ink (fun i:T.CO=> T.send_A (priv i)) F
lemma co_slice (F:RootX G n→ℝ)(hf : germ F): T.coInk F=ink priv (F∘ T.send_A) := (Taylor.ink_ctrl_one _ T.send_A hf).symm
lemma co_cut (F:RootX G n→ℝ)(hf:germ F): ξt (ink tangentVec F) = TT (T.coInk F) := by
  rw [cut_ink T F hf, co_slice _ _ hf]
  change ink tangentVec (((F ∘ T.send_A) ∘ T.bring)) = _
  refine (ink_change T.appear priv tangentVec _ T.bring ?_ ?_).symm
  · intro i
    rcases i with i|i|i|i
    · exact coordinate_in T.bring.toLinearMap i
    all_goals simp [tangentVec,appear]
  exact (show ContDiffAt ℝ ω F (T.send_A 0) from by rw [map_zero]; exact hf).comp 0 T.send_A.contDiff.contDiffAt

lemma tether_A : TieField (intoC T.appear) (fun _ => false) p := by rintro i (_|j|j|j) h <;> first| rfl| exact (h rfl).elim

/-- Factor the restricted Wick rule. -/
abbrev lineCo : Matrix T.CO T.CO ℂ:= (2:ℂ)⁻¹ • intoC T.inverseCo
lemma co_covariance :
    let W:=intoC T.appear
    W * (show Matrix φ φ ℂ from ΣΣ) * Wᵀ=T.lineCo := by
  intro W
  let V:=intoC v
  have hV: Vᵀ*V=1:= by dsimp only [V]; rw [← into_transpose,← into_mul,T.co_inv,into_one]
  rw [sigma_half]; rw [Matrix.mul_smul, Matrix.smul_mul, lineCo]; congr 1
  let U:=sigma (intoC T.Ctilt) (intoC T.fix)
  have ht (i:T.CO) (j:Z G (OEdge n)) : W i (.a j)=Vᵀ i j:= by change (↑(T.takeCo i j) : ℂ)=↑(v j i); rw [← co_T]; rfl
  calc
    W * U * Wᵀ = (Vᵀ*(intoC T.Ctilt)*V) := ?_
    _ = _ := ?_
  · ext i j
    simp_rw [mul_apply,transpose_apply,sum_all (f:=fun x:φ=>_)]
    simp_rw [ht]; unfold W intoC appear
    simp [U,V,sigma]
    rfl
  unfold V Ctilt; simp_rw [into_mul, into_transpose]
  change Vᵀ*(V*_ *Vᵀ)*V = _; simp_rw [Matrix.mul_assoc]; rw [hV,Matrix.mul_one,← Matrix.mul_assoc,hV,one_mul]

lemma slice_view (F: Raw T.CO ℂ)(hf:F∈ Mini _): View ΣΣ (TT F)= View T.lineCo F:= by
  rw [view_change (K:=(show Matrix φ φ ℂ from ΣΣ)) _ F hf, show intoC T.appear * _ * (intoC T.appear)ᵀ= T.lineCo from T.co_covariance]

end YM.FVA2.Inversion.Choice
