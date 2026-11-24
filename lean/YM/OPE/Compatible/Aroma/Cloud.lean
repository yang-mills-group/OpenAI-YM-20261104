import YM.OPE.Compatible.Aroma.Spoke
/-! # Translation w/∆ and conjugacy -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W K:Type*} {L: Side}
namespace Script
open Page
variable {B:Row I J}{v w:fieldX J}
-- act arbitrary linear map WITH f∞ support boundary shifts
abbrev sea (i:J)(v:fieldX J):Cover→ℝ:=fun p=> v (p,i)
def swipe (k:Axis):fieldX J→ₗ[ℝ] fieldX J:=LinearMap.pi fun p:Cover × J=> (LinearMap.proj (R:=ℝ) (φ:=fun _:Cover×J=>ℝ) (p.1+step k,p.2))-LinearMap.proj p
def roamsX (p: Fin n→Axis):fieldX J →ₗ[ℝ] fieldX J:= LinearMap.pi fun i:Cover×J=> LinearMap.proj i.1 ∘ₗ trainX ℝ n p ∘ₗ (LinearMap.pi fun v:Cover=>LinearMap.proj (v,i.2))
lemma roams_eq (p: Fin n→Axis)(x):roamsX p v x=trainX ℝ n p (sea x.2 v) x.1:=rfl
lemma swipeGear (i:Axis)(p:Fin n→Axis)(v:fieldX J): roamsX (Fin.cons i p) v= roamsX p (swipe i v):=by
    ext1 u; rw [roams_eq,trainX,Fin.tail_cons,Fin.cons_zero];rfl
lemma swipeQuiet (h: Quiet v m)(i:Axis): Quiet (swipe i v) m:=by
    obtain ⟨C,hc,g⟩:=h; refine ⟨C*2^m+C,by positivity,fun p=>?_⟩; change ‖v _-v p‖≤ _; apply (norm_sub_le ..).trans; rw [add_mul,mul_assoc]; exact add_le_add ((g (p.1+step _,p.2)).trans (mul_le_mul_of_nonneg_left (ascentStep ..) hc)) (g _)
variable [Fintype J]
lemma swipeA (h:Whole B)(hp:Quiet v m)(i:Axis): meetsX B (swipe i v)=swipe i (meetsX B v):=by
   ext1 x; change _= meetsX B v (x.1+step i,x.2)-meetsX B v x; unfold meetsX; let z(y: Cover × J) := B x.2 y.2 y.1*v (x.1+step i+y.1,y.2) -- args
   rw [← Summable.tsum_sub (show Summable z from meets_current h hp ..) (meets_current h hp ..)]; refine tsum_congr fun j=>?_ ; unfold z; rw [show x.1+step i+j.1=x.1+j.1+step i by abel,← mul_sub];rfl
lemma swarm (h:Whole B)(p:Fin n→Axis)(hp:Quiet v m): meetsX B (roamsX p v)=roamsX p (meetsX B v):=by
    induction n generalizing v with
    | zero=>rfl
    | succ n ih=> rw [← (show Fin.cons (p 0) (Fin.tail p)=p from Fin.cons_self_tail _),swipeGear,swipeGear,← swipeA h hp,ih _ (swipeQuiet hp _)] -- ih order
omit [Fintype J] in
lemma wholeZero [Fintype I](_h:Whole B)(x:I)(y:J) : Complex.re ((B.read 0) x y)=(∑' i,B x y i):=by
    have hu: B.read 0 x y= ∑' i,(↑(B x y i):ℂ):=by
       unfold Row.read Laurent.read; simp [mode]
    rw [hu, ← Complex.ofReal_tsum]; simp
variable [DecidableEq J]
lemma axis_mem (R:Row J J)(h:Whole R)(hp:R.read 0=1)(u:J→ℝ): meetsX R (fun i=>u i.2)=fun i=>u i.2:=by
    ext1 ⟨x,k⟩; have he:Quiet (fun p:Cover×J=>u p.2) 0:=⟨‖u‖,norm_nonneg _,fun p=>(norm_le_pi_norm u _).trans_eq (by unfold poise; ring)⟩
    have hg:= meets_current h he x k; let z(j:Cover)(i:J):= R k i j*u i; change Summable (uncurry z) at hg; unfold meetsX; change (∑' i,uncurry z i)=_
    rw [hg.tsum_prod]; simp only [uncurry_apply_pair]; rw [← hg.tsum_comm,tsum_fintype]; unfold z; simp_rw [tsum_mul_right,← wholeZero h, hp,Matrix.one_apply]; simp [apply_ite Complex.re]
end Script
end YM.OPE.Flume
