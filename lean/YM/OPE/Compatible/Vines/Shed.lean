import YM.OPE.Compatible.Vines.Shore
/-! Gradient pinning for off-shell jet conservation. General homogeneous leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor ContinuousMultilinearMap WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{G:Gauge}
namespace Script
open Page
abbrev Shade (G:Gauge):= Palette G.ColorIndex
abbrev Ridge (G:Gauge)(d:ℕ):= Axis→ Tensor.T E4 G.Color d
def rosary (T:Ridge G d): Tensor.T E4 G.Color (d+1):=
    ((d+1:ℕ):ℝ)⁻¹ • ∑ i, added (T i) (compAxis i)
def warp (T: Ridge G d): Ridge G d:= fun i=> symmetrize (T i) - ((d+1:ℕ):ℝ) • (rosary T).curryLeft (basis i)
lemma rose (T:Ridge G d): Sym (rosary T):=fun z s=> by simp only [rosary,smul_apply,_root_.sum_apply,added_sym _ _ z s]
lemma warpDiag (T:Ridge G d)(i:Axis)(x:E4): diagonal (warp T i) x=diagonal (T i) x- grad i (diagonal (rosary T)) x:=by
    rw [grad, Analysis.D, differential_diagonal _ (rose T)]; change diagonal (symmetrize (T i)) x- (((d+1:ℕ):ℝ) • _) = _; rw [symmetrize_diagonal,Nat.cast_smul_eq_nsmul]; rfl
lemma warpRad (T:Ridge G d)(x:E4):∑ i:Axis,x i • diagonal (warp T i) x=0:=by
    simp_rw [warpDiag,smul_sub]; rw [sum_sub_distrib, grad_euler _ (rose T)]; suffices h:((d+1:ℕ):ℝ) • diagonal (rosary T) x=∑ i:Axis,x i • diagonal (T i) x by rw [h, sub_self]
    have he: diagonal (rosary T) x=((d+1:ℕ):ℝ)⁻¹ • ∑ i:Axis,x i • diagonal (T i) x:=by
       unfold rosary diagonal; rw [smul_apply,_root_.sum_apply]; congr 1; exact sum_congr rfl fun i _=> added_diag ..
    rw [he, smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
def fry (T:Ridge G (d+1)): Taylor G d:=⟨warp T,⟨fun i z s=>by simp only [warp,smul_apply,sub_apply,symmetrize_sym _ z s, freeze_sym _ (rose T) (basis i) z s], warpRad T⟩⟩
lemma warp_base (T:Ridge G 0)(j:Axis)(x:E4): diagonal (warp T j) x=0:=by
    rw [show diagonal (warp T j) x=diagonal (warp T j) (basis j) from congr_arg (warp T j) (Subsingleton.elim ..)]
    have hx:=warpRad T (basis j); simpa using hx
abbrev letterX (T:Tensor.T E4 G.Color d): fieldX G.ColorIndex:=fun x=> (diagonal T (fromX (translit x.1))) x.2
abbrev ledge (T:Ridge G d): fieldX (Shade G):=fun x=> letterX (T x.2.1) (x.1,x.2.2)
abbrev driftX (T: Ridge G d):= letterX (rosary T)
lemma letterL (T: Tensor.T E4 G.Color d): Low (letterX T) d:=fun t=> by
    let R: G.Color →L[ℝ] ℝ := EuclideanSpace.proj t; exact ⟨_, tgon (R.compContinuousMultilinearMap T), fun _=>rfl⟩
lemma ledgeL (T:Ridge G d):Low (ledge T) d:=fun i=> letterL (T i.1) i.2
-- seam polynomial gradient decomposition after ignoring lower
abbrev debtX (T:Ridge G d):= ledge T -mountain (driftX T)-ledge (warp T)
lemma cast_step (x:Cover)(a:Axis):fromX (translit (x+step a)) = fromX (translit x)+basis a:=by ext i; by_cases h:i=a<;>simp [translit,fromX,h,Lattice.step,basis]
lemma ridgeL (T:Ridge G d)(a: Shade G):∃ f∈Flavor Axis (d-1), (d=0→ f=0)∧∀ x:Cover, debtX T (x,a)= f (translit x):=by
    let R:= rosary T; let D: G.Color→L[ℝ]ℝ:=EuclideanSpace.proj a.2; let F:=D.compContinuousMultilinearMap R; let f:= diagonal F ∘ fromX; let x:=basis a.1
    obtain ⟨hx,hh⟩:=tailP f (tgon F) x
    have hp:d+1-2=d-1:=by omega
    rw [hp] at hx; refine ⟨-(gust x f-breeze x f),(Flavor Axis _).neg_mem hx,fun h=>by rw [hh (by omega),sub_self,neg_zero],fun i=>?_⟩; let j:=fromX (translit i)
    have h(i:Cover):mountain (driftX T) (i,a)= gust x f (translit i):=by change diagonal R (fromX (translit (i+step a.1))) a.2-_ =_; rw [cast_step]; rfl
    change diagonal (T a.1) j a.2 -mountain _ (i,a)-diagonal (warp T a.1) j a.2=_; rw [h, warpDiag T]; have hv := fderiv_comp j D.differentiableAt ((diag_smooth R ⊤).differentiable (by simp) j); have he: breeze x f (translit i)=D (grad a.1 (diagonal (rosary T)) j):=by unfold breeze; rw [show f∘invertX = D ∘ diagonal R from rfl,hv,D.fderiv];rfl
    rw [Pi.neg_apply,Pi.sub_apply,he]; change _-_ - (diagonal (T a.1) j a.2 - (grad a.1 (diagonal R) j) a.2)= -(_- grad a.1 (diagonal R) j a.2); ring
lemma wind_quiet (T:Ridge G d): Quiet (debtX T) (d-1):= low_quiet fun a=> by obtain ⟨f,h,-,he⟩:=ridgeL T a; exact ⟨f,h,he⟩
lemma ridge_base (T:Ridge G 0): ledge T= mountain (driftX T):=by
    ext1 p; obtain ⟨x,i⟩:=p; obtain ⟨f,h,hh,g⟩:= ridgeL T i; specialize g x; change ledge T (x,i)- mountain _ (x,i)-diagonal (warp T i.1) _ i.2= _ at g; rw [warp_base,hh rfl] at g; simpa [sub_eq_zero] using g
end Script
end YM.OPE.Flume
