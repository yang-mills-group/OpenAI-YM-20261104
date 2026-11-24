import YM.RG11Proof.Rigidity.Theater

/-!
# Collect an actual color rotation, when Gram observables are available on
both tracks as (fixed) data. No smooth selection of rotations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free Prism Function Metric
open scoped Topology BigOperators InnerProductSpace Classical

variable {G : Gauge} {I : Type}

local notation "X"=>G.Color
abbrev Wheel (G : Gauge) := G.Color ≃ₗᵢ[ℝ] G.Color

def grid (M : Mirror G) : X→ₗ[ℝ] X where
  toFun x:= WithLp.toLp 2 fun i=>∑ j:G.ColorIndex, M (i,j)*x j
  map_add' x y:= by ext1 i; change (∑ j:G.ColorIndex,M (i,j)*(x j+y j))=(∑ j:G.ColorIndex, M (i,j)*x j) + ∑ j:G.ColorIndex,M (i,j)*y j; simp [mul_add,Finset.sum_add_distrib]
  map_smul' a x:= by ext1 i; change (∑ j:G.ColorIndex,M (i,j)*(a*x j))=a*∑ j:G.ColorIndex,M (i,j)*x j; simp_rw [mul_left_comm _ a,Finset.mul_sum]
def board (G : Gauge) : Mirror G:= WithLp.toLp 2 fun i=> if i.1=i.2 then 1 else 0
lemma grid_board (x : X) : grid (board G) x=x := by
  ext1 i; change (∑ j:G.ColorIndex,(if i=j then (1:ℝ) else 0)*_)=_; simp [ite_mul]
def roster (E : Wheel G) : Mirror G:= WithLp.toLp 2 fun i=> E (unitColor G i.2) i.1
lemma grid_roster (E : Wheel G) (x : X) : grid (roster E) x=E x := by
  have he : ∑ i:G.ColorIndex, x i • unitColor G i=x := color_sum ..
  conv_rhs=>rw [← he,map_sum]
  ext1 i
  simp_rw [map_smul] -- piLp evaluation
  change (∑ j:G.ColorIndex, E (unitColor G j) i*x j)=_
  simp [mul_comm]
lemma unit_apply (M:Mirror G)(i j:G.ColorIndex) : grid M (unitColor G i) j=M (j,i):=by change (∑ b:G.ColorIndex,M (j,b)*unitColor G i b)=_; simp [unitPaint,mul_ite]

lemma charged (M : Mirror G) (hM : ∀ v : X, ‖grid M v‖^2=‖v‖^2) : ∃ E : Wheel G, M=roster E := by
  let Q : X →ₗᵢ[ℝ] X:={grid M with norm_map' := fun x=> sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp (hM x)}
  have hi : Injective (grid M) := Q.injective
  have h : Bijective (grid M) := ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
  let E : Wheel G:={LinearEquiv.ofBijective (grid M) h with norm_map':=Q.norm_map}
  refine ⟨E,?_⟩
  ext1 i; change M i = grid M (unitColor G i.2) i.1; rw [unit_apply]

def Gram (A B : Performer G I) : Prop := ∃ i : I, ∃ q : X → System,
    ∀ v : X, ∀ M:Mirror G, A.data (i,q v) M=‖grid M v‖^2 ∧ B.data (i,q v) M=‖grid M v‖^2

def corot (s : ℝ) (q : System (G:=G)) : System (G:=G) := fun i j=>s • q i j

lemma top_shift (Y : Cast G) (N : ℕ)(q : System)(s : ℝ)(M:Mirror G) :
    topSample Y N (corot s q) M=topSample Y N q (s • M) := by
  unfold topSample; congr 1; funext i; unfold corot
  simp [PiLp.smul_apply,smul_eq_mul,map_smul, mul_left_comm, mul_assoc]

lemma theirs (c : G.ColorIndex) {A B : Performer G I} (h : Desert A B) (g : Gram A B) :
    ∃ E : Wheel G, ∀ (i:I)(q:System), A.data (i,q) (board G)=B.data (i,q) (roster E) := by
  let v:= board G
  let s:= (1+ ‖v‖)⁻¹
  have hs : s≠0 := by unfold s; positivity
  have ha : s • v ∈ ball (0:Mirror G) 1:= by simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<s by unfold s; positivity)]; unfold s; rw [inv_mul_lt_iff₀ (by positivity)]; linarith
  obtain ⟨b,hb,he⟩:= Prism.interview (h.cast_shot c) (fun _=>samples_cont ..) (fun _=>samples_cont ..) ha
  · let M := s⁻¹ • b
    have hh (i : I)(q : System) : A.data (i,q) (board G)=B.data (i,q) M := by
      have ht:= he (i,corot s⁻¹ q)
      unfold Performer.data at ht ⊢ -- risky goal hypotheses use dsimp
      dsimp only at ht ⊢; rw [top_shift,top_shift,inv_smul_smul₀ hs] at ht; exact ht
    obtain ⟨i,q,H⟩:=g
    have hM (a : X) := (H a M).2.symm.trans ((hh i (q a)).symm.trans (H a _).1)
    simp_rw [grid_board] at hM
    obtain ⟨k,hk⟩:=charged M hM
    exact ⟨k,fun i q=> hk ▸ hh i q⟩
end YM.RG11.Rigidity
