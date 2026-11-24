import YM.RGComparison.Core16.Lumen.Verse

/-! # The projected Taylor pieces have literal receipts in THIS curvature-chart gloss
Order/r not hide factorial or g. Works off masks for this part, before expectation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open Planet Finset
open PertExtension PertExtension.Series Tested Radial
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G : Gauge}{ι L k T A D:Type}
lemma mono_cone (x:G.Color)(i:G.ColorIndex): |x i| ≤ ‖x‖ := by
    rw [← EuclideanSpace.basisFun_inner]; convert (abs_real_inner_le_norm (colors G i) x) using 1; simp

abbrev Stuff (G:Gauge)(ι L:Type):= L→(ι ⊕ G.Color)

def book (p:Stuff G ι L) (g:ℝ)(x:Sky G ι)(i:L):G.Color:= Sum.elim (fun j=> g⁻¹ • G.curvature (x j)) id (p i)
def celery (p: Stuff G ι L)(S:Finset ι)(Q:ℝ):=∀ i:L, Sum.elim (·∈S) (fun y=>‖y‖ ≤ Q) (p i)
def tell (p:Stuff G ι L)(i:Wire G L)(g:ℝ)(x:Sky G ι):ℝ:= book p g x i.1 i.2
variable {p:Stuff G ι L}{S:Finset ι}{Q:ℝ}(hp:celery p S Q)
include hp
lemma offers_tell (j:Wire G L) (he:0 ≤ Q): Offers 1 (Q+1) (tell p j):= by
    let i:=j.1; have hx:=hp i; rcases ha:p i with u|w
    · rw [show tell p j=sing [(u,j.2)] from funext fun g=>funext fun x=>?_]
      · exact .raise (.words [(u,j.2)] le_rfl) (by linarith)
      · change book p g x i j.2=_; unfold book; rw [ha]; simp [sing, tally,curve,div_eq_mul_inv,mul_comm]
    rw [show tell p j=fun _ _=> w j.2 from (funext fun g=> funext fun x=> by change book p g x i j.2=_; unfold book; rw [ha]; rfl)]
    rw [ha] at hx; exact (Offers.flat ..).raise (((mono_cone w j.2).trans (show ‖w‖ ≤ Q from hx)).trans (le_add_of_nonneg_right zero_le_one))
variable [Fintype L]
omit hp in
lemma treasury (p: Stuff G ι L)(g:ℝ)(x:Sky G ι):book p g x=∑ i:Wire G L, tell p i g x • one i:= by
    rw [repr]; rfl

def tale (p: Stuff G ι L)(ψ:(L→G.Color)→ℝ)(j:ℕ): Melody G ι:=fun g x=> jet ψ j (book p g x)

def presence (ψ:(L→G.Color)→ℝ) (q:ℝ)(j:ℕ):ℝ:= ∑ i:Fin j → Wire G L, |YM.Tensor.coeff ψ j 0 (fun u=> one (i u))| * (q+1)^j
lemma story (ψ:(L→G.Color)→ℝ) (he:0 ≤ Q) (j:ℕ): Offers j (presence ψ Q j) (tale p ψ j) := by
    let C (r:Fin j→ Wire G L):= YM.Tensor.coeff ψ j 0 (fun i=> one (r i))
    let F (r:Fin j→ Wire G L): Melody G ι:= C r • ∏ i,tell p (r i); let V g x: L→G.Color:= book p g x
    have h:tale p ψ j=∑ i,F i:=by
       funext g x; rw [Finset.sum_apply]; simp only [Finset.sum_apply]; change Tensor.diagonal (YM.Tensor.coeff ψ j 0) (V g x)= _
       unfold Tensor.diagonal; rw [show (fun _ : Fin j=> V g x)= (fun _=> ∑ i: Wire G L,tell p i g x • one i) from funext (fun i=> treasury p g x),(YM.Tensor.coeff ψ j 0).map_sum (α:=fun _=> Wire G L) (fun _ i=>tell p i g x • one i)]
       refine sum_congr rfl fun i _=>?_ ; unfold F; rw [(YM.Tensor.coeff ψ j 0).map_smul_univ (fun u: Fin j=>tell p (i u) g x), Pi.smul_apply,Pi.smul_apply, smul_eq_mul,smul_eq_mul]; simp_rw [Finset.prod_apply]; exact mul_comm _ _
    rw [h]; refine Offers.finance F (fun i=> |C i| * (Q+1)^j) _ fun i _=> ?_
    have hh := Offers.team (tell p ∘ i) (fun _=> Q+1) univ (fun j _=> offers_tell hp (i j) he)
    apply Offers.scale _ (p:=∏ j,tell p (i j)); simp only [prod_const,card_univ,Fintype.card_fin,mul_one] at hh; exact hh
end YM.RGComparison.Core16.Lumen
