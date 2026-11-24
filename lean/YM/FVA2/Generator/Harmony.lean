import YM.FVA2.Generator.Exterior
/-!
# The projected true-physical Taylor columns at the exterior resonance satisfy Clean

Available before taking annulus limits (it's on the scaling leading term, not on the sampled lattice
coefficient). NB a `Tune` by itself need not be Clean! We use the ACTUAL TaylorTower data; $F$ co-closed implies that the homogeneous radial axial potential has zero divergence, hence also zero Laplacian. This
works even when $e^0$ positions are not chosen along any axes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Harmony
open Function Set Filter XSpace Center XSpace.Litter XSpace.Scale XSpace.Trace XSpace.Lows RG12.Strike Maxwell Further.FreeCovariance.KP Tensor
open Exterior
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n m d:ℕ}
section Shell
variable (A:Maxwell.Shell G d)(j:Axis)(x:E4)
private def B (i:Axis) := motifValue ( (roll A).val i )
private lemma hose (i:Axis)(x:E4) : B A i x=((↑(d+2:ℕ):ℝ))⁻¹ • ∑ j:Axis,x j • Tensor.diagonal (A.val j i) x:= contracted_diag (h:=A.property.1) ..
private lemma dr (i k:Axis): grad k (B A i) x=((↑(d+2:ℕ):ℝ))⁻¹ • (diagonal (A.val k i) x+ ∑ j:Axis,x j • grad k (diagonal (A.val j i)) x):= by
    rw [ ← grad_self (fun j=> A.val j i) k x, funext (hose A i), grad, Analysis.D, fderiv_fun_const_smul ]; rfl
    exact DifferentiableAt.fun_sum fun j _=> (compAxis j).differentiableAt.smul ( (diag_smooth _ ω).differentiable (by decide) _ )
private lemma solves : ∑ i:Axis, grad i (B A i) x=0:=by
    have ht : ClosedJet A.val:= A.property.1
    have hx(i:Axis): diagonal (A.val i i) x=0:=congr_arg (fun T=>diagonal T x) (smul_right_injective (a₁:=A.val i i) (a₂:=0) (r:=(2:ℝ)) (T E4 G.Color d) (by norm_num) (by dsimp only; rw [smul_zero,two_smul]; nth_rw 1 [ht.antisymmetric]; simp) ) -- exists?
    have hh (j i:Axis): grad i (diagonal (A.val j i)) x= -grad i (diagonal (A.val i j)) x:=by
       nth_rw 1 [ht.antisymmetric]; change fderiv ℝ (-diagonal (A.val i j)) x _= _; rw [fderiv_neg]; rfl
    simp_rw [dr,hx,zero_add,← Finset.smul_sum]; rw [Finset.sum_comm]; rw [Finset.sum_eq_zero (f:= fun j=> ∑ i:Axis,x j • grad i (diagonal (A.val j i)) x), smul_zero ]; intro j _; rw [ ← Finset.smul_sum, Finset.sum_congr rfl (fun i _=> hh j i),Finset.sum_neg_distrib,A.property.2 j x,neg_zero,smul_zero ]
private lemma smooth (m:ℕ∞ω)(i:Axis) : ContDiffAt ℝ m (B A i) x:= (diag_smooth _ _).contDiffAt
private lemma press : ∑ i:Axis, grad i (grad i (B A j)) x=0:=by
    let f(i:Axis) := grad i (B A i); have he (i j:Axis) : DifferentiableAt ℝ (grad i (B A j)) x := (grad_smooth _ (smooth A x ω _) (by exact le_top : ω+1≤ω)).differentiableAt (by decide)
    have hh(i:Axis): grad i (diagonal (A.val i j)) x= grad i (grad i (B A j)) x-grad j (f i) x:=by
       rw [← match_leg A, takeCurl_diag]; change fderiv ℝ (grad i (B A j)-grad j (B A i)) x (basis i)= _; rw [fderiv_sub (he i j) (he j i)]; change grad i (grad i (B A j)) x - grad i (grad j (B A i)) x=_; rw [grad_comm (smooth A x 2 i) i j]
    obtain H:= A.property.2 j x; rw [Finset.sum_congr rfl (fun i _=> hh i),Finset.sum_sub_distrib] at H; rw [sub_eq_zero.mp H]; rw [← show grad j (fun z=> ∑ i:Axis,f i z) x= (∑ i:Axis, grad j (f i) x) from ?_,funext (solves A)]; simp [grad,Analysis.D]
    unfold grad Analysis.D; rw [fderiv_fun_sum (fun i _=> he i i),sum_apply]

theorem bridge (c:G.ColorIndex): Breeze (fun i=> paint c ∘ B A i) univ:= ⟨fun y _ j=>by
    simp_rw [ ← retrieve (paint c) isOpen_univ (fun t (_ht:Set.Mem univ t)=> smooth A t ω j) (Set.mem_univ y) ]; rw [← map_sum]; change paint c (∑ i:Axis,grad i (grad i (B A j)) y)=_; rw [press, map_zero], fun y _=>by
    rw [Finset.sum_congr rfl (fun i _=>(retrieve (paint c) isOpen_univ (fun t _ => smooth A t ω i) (Set.mem_univ y) [i]).symm), ← map_sum]; change paint c (∑ i:Axis,grad i (B A i) y)=_; rw [solves,map_zero]⟩
end Shell
variable (A:Maxwell.TaylorTower G)(p:Fin (d+1))(c:G.ColorIndex)
theorem clean : Clean (slate (fun i=> panel (Bracket.seat d A) p i c) 0) p.val:= by
    refine jets (fun i=> panel (Bracket.seat d A) p i c) isOpen_univ (fun _=> (graded (paint c) _).jet) ?_ _ (Set.mem_univ _) _
    obtain ⟨p,hp⟩:=p; cases p with
    | zero =>
       constructor
       · intro x _ j; apply Finset.sum_eq_zero; intro i _; change barrage (Exterior.paint c ∘ motifValue _) _ _= _; rw [Exterior.late]; rfl -- test implicit
         exact show 0<[i,i].length by simp
       intro x _; apply Finset.sum_eq_zero; intro i _; change barrage (_ ∘ motifValue _) _ x= _; rw [Exterior.late]; rfl; exact show 0<[i].length by simp
    | succ m => exact bridge (A m) c

variable (V: Hat G d)
lemma bill (j:Axis)(x:E4): screen V (Bond.mk [] j c) p x= τ p.val*sep p.val (slate (fun i=> panel V p i c) 0 j) x:= (graded (paint c) _).paid x
lemma bits (i j:Axis)(x:E4)(ht:p.val≠0): screen V (Bond.mk [i] j c) p x= τ (p.val-1) * sep (p.val-1) (fun l=> slate (fun k=> panel V p k c) 0 j (i::l)) x:=by
   let f:=panel V p j c; let z:=Bond.mk [i] j c; rw [(chains V z p (show 1≤p.val from by omega )).paid x]; congr 2 -- inspect
   funext l; unfold slate; change barrage (barrage f [i]) l 0=barrage f (i::l) 0; rw [←barrage_append]; exact regimen isOpen_univ (show silk univ f from (graded (paint c) _).jet) (Set.mem_univ _) (List.perm_append_comm (l₁:=l) (l₂:=[i]))
end YM.FVA2.Generator.Harmony
