import YM.MSbar.Dim.Polar

/-! Hat metric projection by continuation, Open-index polynomial convention. Not implementing any
d-dimensional reduction to four independent gauge fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical NNReal InnerProductSpace
variable {m n : ℕ} {T : ℕ→ Type} {S : Motion T} {V:Prop}
variable {F : ∀ m,T m × Hat m → ℂ} {K : ℝ}
abbrev fin (m:ℕ) := Fin (2*m)
def basis (m:ℕ) : OrthonormalBasis (fin m) ℝ (Hat m) := EuclideanSpace.basisFun (fin m) ℝ
def index (V:Prop)(m:ℕ): Finset (Hat m):= if V then Finset.univ.image (basis m) else {0}
def metric (S:Motion T) (V:Prop)(s:ℂ)(F:∀ m,T m × Hat m→ ℂ)(m:ℕ)(x:T m):=
    (∑ y∈ index V m,F m (x,y)) -- fix scoping term
        + if V then 2*(s-m)* F (m+1) (above S x,grow m (0, axis)) else 0

namespace Trace
lemma sampling (V:Prop) (F : ∀ m,T m×Hat m→ℂ)(x:T m)(S:Motion T) : metric S V m F m x= ∑ y∈index V m,F m (x,y):= by simp [metric]

private lemma count (F: Hat m→ₗ[ℝ] Hat m→ₗ[ℝ] ℂ) {ι κ:Type*}[Fintype ι][Fintype κ](b: OrthonormalBasis ι ℝ (Hat m)) (c: OrthonormalBasis κ ℝ (Hat m)) : ∑ i,F (b i) (b i)= ∑ i,F (c i) (c i):=by
    calc
     _ = ∑ i:ι,∑ j:κ,⟪c j,b i⟫_ℝ • F (c j) (b i):=by
        simp_rw [← LinearMap.flip_apply F (c _) (b _)];apply Finset.sum_congr rfl;intro j _; simp_rw [← map_smul,← map_sum,c.sum_repr' (b j)]
        rfl
     _ = ∑ j:κ,∑ i:ι,⟪b i,c j⟫_ℝ • F (c j) (b i) := by rw [Finset.sum_comm]; simp_rw [real_inner_comm (c _)]; 
     _ = _ := by apply Finset.sum_congr rfl; intro j _; simp_rw [← map_smul,←map_sum,b.sum_repr' (c j)]
variable (h : (S.prod vectors).Natural F) (hg : ∀ i (x:T i), Two V fun y=> F _ (x,y)) (s : ℂ)
private lemma recipe {ι:Type*}[Fintype ι] (hv:V) (x:T m)(b:OrthonormalBasis ι ℝ (Hat m))(h : ∀ i (x:T i), Two V fun y=> F _ (x,y)): ∑ y∈ index V m,F _ (x,y)=∑ y,F _ (x,b y):=by
    unfold index; rw [if_pos hv,Finset.sum_image]; rotate_left
    · exact (basis m).toBasis.injective.injOn
    obtain hG:= h m x; unfold Two at hG; rw [if_pos hv] at hG; obtain ⟨A,hA⟩:= hG; dsimp only at hA; simp_rw [hA]; exact count A _ _

-- tower bridge. Up at m goes further to evaluate the trace cost.
def step (m) : Hat (m+1) := grow m (0,axis)
lemma edge (m) : ‖step m‖=1:= (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by unfold step; rw [grow_sq]; simp [axis_norm])
lemma orth (m) (y:Hat m): ⟪up m y,step m⟫_ℝ=0:=by rw [step,up_is,grow_inner]; simp
include h hg
lemma inner_up (hv: V) (x:T m): (∑ v∈ index V (m+1), F _ (above S x,v))=(∑ v∈ index V m,F m (x,v))+2* F _ (above S x, step m) := by
    let e:= assemble m 1 _ rfl
    let q:= ((basis m).prod (basis 1)).map e; rw [recipe hv (above S x) q hg,Fintype.sum_sum_type]; simp_rw [q,OrthonormalBasis.map_apply,OrthonormalBasis.prod_apply]; simp only [Sum.elim_inl, Sum.elim_inr,comp_apply]
    congr! 1
    · rw [recipe hv x (basis m) hg]; apply Finset.sum_congr rfl; intro i hi; exact Tower.rotate h (up m) x _
    have ht(a:fin 1): F _ (above S x,grow m (0,basis 1 a))=F _ (above S x, step m):=Tower.plans h x 0 ((basis 1).norm_eq_one a|>.trans axis_norm.symm)
    change ∑ a:fin 1,F _ (above S x,grow m (0,basis 1 a))= _; simp_rw [ht]; simp [fin]
lemma shifted (x:T m): F _ (above S (above S x), step (m+1))=F _ (above S x, step m):= by
    let W : Move m (m+2):= (up (m+1)).comp (up m)
    have he:above S (above S x)=S.move W x := (S.together ..).symm
    rw [← Tower.rotate h (up (m+1)) (above S x) (step m)]; change _=F _ (above S (above S x),_); rw [he]
    apply Tower.radial_point h x W
    · rw [(up (m+1)).norm_map,edge,edge]
    intro y; change ⟪up _ (up _ y),_⟫_ℝ= ⟪up _ (up _ y),_⟫_ℝ; rw [orth, LinearIsometry.inner_map_map,orth]
lemma advance (x:T m) : metric S V s F (m+1) (above S x)=metric S V s F _ x:= by
    unfold metric; split_ifs with hv; swap; exact (by unfold index; rw [if_neg hv,if_neg hv]; simpa [-up_is] using! (Tower.rotate h (up m) x 0))
    rw [inner_up h hg hv]; rw [show grow m (0,axis)=step m from rfl,show grow (m+1) (0,axis)=step _ from rfl,shifted h hg]; push_cast; ring
private lemma spin {m:ℕ} (P:Hat m≃ₗᵢ[ℝ] Hat m)(x:T m): metric S V s F _ (S.move P.toLinearIsometry x)=metric S V s F _ x:= by
    let q:= S.move P.toLinearIsometry x; change metric _ _ _ _ m q=_; unfold metric; split_ifs with hv; swap; exact (by unfold index; rw [if_neg hv]; simpa [q] using! Tower.rotate h P.toLinearIsometry x 0)
    rw [recipe hv q ((basis m).map P) hg,recipe hv x (basis m) hg]; obtain ⟨W,hW⟩:= spin_growth P (LinearIsometryEquiv.refl ℝ _)
    congr! 1
    · exact Finset.sum_congr rfl fun i _=> Tower.rotate h P.toLinearIsometry _ _
    have hs: S.move W.toLinearIsometry (above S x)= above S q:=by unfold above q; simp_rw [← S.together]; exact congr_arg (fun (W:Move m (m+1))=> S.move W x) (DFunLike.ext _ _ fun y=> hW (y,0))
    have he:W (grow m (0,axis))=grow m (0,axis):=by rw [hW];simp
    refine congr_arg (fun x:ℂ=>(2*(s-m))*x) ?_; rw [← hs]; exact (by simpa only [LinearIsometryEquiv.coe_toLinearIsometry, he] using Tower.rotate h W.toLinearIsometry (above S x) (grow m (0,axis)))
lemma coherent : S.Natural (metric S V s F):= S.reaches (fun i P x=> spin h hg s P x) (fun m x=> advance h hg s x)
end Trace
end YM.MSbar.Dim
