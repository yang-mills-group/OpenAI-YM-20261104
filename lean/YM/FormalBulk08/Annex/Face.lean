import YM.FormalBulk08.Annex.Tame
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Lattice Matrix Dawn Set
open scoped BigOperators Topology ENNReal Classical ContDiff Matrix
variable {D k: ℕ}
variable (a:Axis)(b:Bool)
def taps (D:ℕ) (i:Fin (D+1)):ℝ:= -((20+i.val:ℕ):ℝ)⁻¹
lemma gentle (i:Fin (D+1)): -1/20≤taps D i ∧ taps D i≤0:= by
   unfold taps; have hx: ((20:ℕ)+i.val:ℝ)≥20:= le_add_of_nonneg_right (Nat.cast_nonneg _)
   refine ⟨?_,neg_nonpos_of_nonneg (by positivity)⟩; push_cast; rw [neg_div,one_div,neg_le_neg_iff]; exact inv_anti₀ (by norm_num) (by push_cast at *;exact hx)
lemma inject_tap (D:ℕ): Injective (taps D):= by
   intro i j p; apply Fin.ext; simpa [taps] using p

def treks (D:ℕ): Fin (D+1) →ℝ:= (fun _=>1) ᵥ* (vandermonde (taps D))⁻¹
lemma forest (j: Fin (D+1)):∑ i,treks D i*taps D i ^j.val=1:= by
   have ht:= isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr (inject_tap D))
   exact congr_fun (show (treks D ᵥ* (vandermonde (taps D)))= (fun _=>1) from (by unfold treks; rw [vecMul_vecMul,nonsing_inv_mul _ ht,vecMul_one])) j

def rounds (f:Garden D):Garden D:= ∑ i,treks D i • useBasis a b (taps D i) f
lemma map_basis (f:Garden D)(x:E4)(u:Brush D) : halo (rounds a b f) u x= ∑ i, treks D i*halo (useBasis a b (taps D i) f) u x:=by
    unfold rounds; generalize (Finset.univ:Finset (Fin (D+1)))=S
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; unfold Dawn.halo; change iteratedFDeriv ℝ _ 0 x _=0; simp
    | insert i s h ih=>
       rw [Finset.sum_insert h,Finset.sum_insert h]; unfold Dawn.halo at *; rw [Submodule.coe_add,iteratedFDeriv_add_apply (tends _ u.1|>.contDiffAt) (tends _ u.1|>.contDiffAt)];rw [← ih]; rw [show ( (treks D i • useBasis a b (taps D i) f):Garden D).val=treks D i • (useBasis a b (taps D i) f).val from rfl, iteratedFDeriv_const_smul_apply ((tends _ u.1).contDiffAt)]; rfl
lemma agreement (f:Garden D)(x:E4)(h:x a=border b)(k:ℕ)(hp:k≤D): iteratedFDeriv ℝ k (rounds a b f).val x=iteratedFDeriv ℝ k f.val x:= by
   apply views; intro i; let y:Brush D:= ⟨⟨k,Nat.lt_succ_of_le hp⟩,i⟩; change halo (rounds a b f) y x=halo f y x
   let n:= (Finset.univ.filter fun u=> a=i u).card; have he:n ≤ D:= by
       unfold n; exact (Finset.card_filter_le ..).trans (by simpa using hp)
   rw [map_basis]; simp_rw [folded, jostle_border a b _ x h,←mul_assoc,←Finset.sum_mul]; change (∑ i,treks D i * taps D i^n)*_= _;rw [show n=(⟨n,Nat.lt_succ_of_le he⟩:Fin (D+1)).val from rfl,forest,one_mul]

def nearM : Set E4:= {x | ε b*x a ≤ ε b*border b}
def farM : Set E4:= {x | ε b*border b≤ ε b*x a}
lemma coverM : nearM a b ∪ farM a b=Set.univ:=eq_univ_iff_forall.mpr fun x=> le_total (ε b*x a) (ε b*border b)
lemma near_border {x:E4}(h:x∈ nearM a b)(hp:x∈farM a b): x a=border b:= mul_left_cancel₀ (show ε b≠0 by cases b<;> simp [ε]) (le_antisymm h hp)
lemma near_closed : IsClosed (nearM a b):=isClosed_le (continuous_const.mul (shadeP a).continuous) continuous_const
lemma far_closed : IsClosed (farM a b):=isClosed_le continuous_const (continuous_const.mul (shadeP a).continuous)

def crack (f:Garden D)(x:E4):ℝ:= if x∈nearM a b then f.val x else (rounds a b f).val x
lemma brack (f:Garden D):
    ContDiff ℝ D (crack a b f) ∧ ∀ u:ℕ,u≤D → EqOn (iteratedFDeriv ℝ u (crack a b f)) (iteratedFDeriv ℝ u f.val) (nearM a b) ∧ EqOn (iteratedFDeriv ℝ u (crack a b f)) (iteratedFDeriv ℝ u (rounds a b f).val) (farM a b) := by
   refine pieceD (near_closed ..) (far_closed ..) (coverM ..) f.property (rounds a b f).property (fun x h=> if_pos h) (fun x h=> ?_) (fun m hp x hx=> (agreement a b f x (near_border a b hx.1 hx.2) _ hp).symm)
   by_cases hp: x∈nearM a b
   · unfold crack; rw [if_pos hp]; nth_rw 1 [← iteratedFDeriv_zero_apply (𝕜:=ℝ) (m:=Fin.elim0) (f:=f.val) (x:=x)]; rw [← agreement a b f x (near_border a b hp h) _ (Nat.zero_le D),iteratedFDeriv_zero_apply] -- parameters
   exact if_neg hp

def notchM (f:Garden D): Garden D:= ⟨crack a b f,(brack a b f).1⟩
lemma quiet (f: Garden D)(u:Brush D)(x:E4)(h:x∈nearM a b): halo (notchM a b f) u x=halo f u x:= by
   change iteratedFDeriv ℝ _ (crack _ _ _) _ _= _; rw [((brack a b f).2 u.1.val (Nat.le_of_lt_succ u.1.isLt)).1 h];rfl
lemma further (f:Garden D)(u:Brush D)(x:E4)(h:x∈farM a b):halo (notchM a b f) u x=halo (rounds a b f) u x:= by
   change iteratedFDeriv ℝ _ (crack _ _ _) _ _=_;rw [((brack a b f).2 u.1.val (Nat.le_of_lt_succ u.1.isLt)).2 h];rfl
end YM.FormalBulk08.Annex
