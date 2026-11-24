import YM.XSpace.Crush

/-!
# Local gauge pressure split at cutoff multiplication (keep complete boundary)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Prelude
open Lattice Sail Scale Trace Future Mu Function Set Filter Chart2 MvPolynomial Next.Rank.Normal Finsupp
open scoped Topology BigOperators InnerProductSpace ContDiff
variable {G:Gauge}{c:Shade.Cut}{n d:ℕ}
abbrev Mark := Cover→₀ℂ
def sibling (x:Mark)(d:Axis):Mark:= Finsupp.mapDomain (fun p:Cover=>p+step d) x-x
lemma sibling_at (x:Mark)(j:Axis)(p:Cover): sibling x j p=x (p-step j)-x p:= by
  have he:=Finsupp.mapDomain_apply (Equiv.addRight (step j:Cover)).injective x (p-step j); change mapDomain (fun p:Cover=>p+step j) x (p-step j+step j)=_ at he; rw [sub_add_cancel] at he; rw [sibling,Finsupp.sub_apply,he]
section
variable {I T:Type*}{W:Type*}[AddCommGroup T][Module ℂ T][AddCommGroup W][Module ℂ W]
def send (c:Mark) : (Cover→T)→ₗ[ℂ] T:=∑ i∈c.support,c i • LinearMap.proj i
lemma sends (x:Mark)(u:Cover→T): send x u=linearCombination ℂ u x:=by unfold send; rw [LinearMap.sum_apply];rfl
lemma by_send (f:T→ₗ[ℂ] W)(x:Mark)(g:Cover→T): f (send x g)=send x (fun i=>f (g i)):=by unfold send; simp only [LinearMap.sum_apply, _root_.map_sum, LinearMap.smul_apply,LinearMap.proj_apply,map_smul]
lemma send_many (s:Finset I)(x:Mark)(f:I→Cover→T): (∑ i∈s,send x (f i))=send x (fun y=>∑ i∈s,f i y):=by unfold send; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply, Finset.smul_sum]; exact Finset.sum_comm
lemma contour (c:Mark)(i:Axis)(f:Cover→ℂ)(g:Cover→ℂ): send c (fun z=> f z*(g (z+ step i)-g z))=
      send c (fun z=> (f (z-step i)-f z)*g z)+send (sibling c i) (fun z=> f (z-step i)*g z):=by
  simp only [sends,sibling,_root_.map_sub,linearCombination_mapDomain,comp_def,add_sub_cancel_right]
  simp_rw [linearCombination_apply,Finsupp.sum, sub_mul,mul_sub]; simp only [smul_sub,Finset.sum_sub_distrib]; abel
end

lemma ticket_price (x:Cover)(A B:Contact G): (∑ q:PlaqAxes, ↑(inner ℝ (linearFace (x,q) A) (linearFace (x,q) B)):ℂ)=∑ i:Axis,∑ j:Axis,∑ c:G.ColorIndex,(↑(crackle i j A x c):ℂ)*(↑(B (x+ step i,j) c)- ↑(B (x,j) c)):=by
  let p (i j:Axis):ℝ:= ∑ c:G.ColorIndex,crackle i j A x c*(B (x+step i,j) c-B (x,j) c); have he(i:Axis):p i i=0:=by unfold p; simp [crackle_ap]
  have he:= Feynman.order_cost p he
  rw [Finset.sum_comm] at he
  conv_rhs=> rw [show (∑ i:Axis,∑ j:Axis,∑ c:G.ColorIndex,(↑(crackle i j A x c):ℂ)*(↑(B (x+ step i,j) c)- ↑(B (x,j) c)))=(∑ i:Axis,∑ j:Axis,p i j :ℝ) by push_cast [p]; rfl]
  rw [he, Complex.ofReal_sum]; refine Finset.sum_congr rfl fun q _=>?_; congr 1
  let i:= q.val.1; let j:=q.val.2
  rw [show linearFace (G:=G) (x,q) A=crackle i j A x from (plot i j q.property x A).symm]; unfold p; rw [← Finset.sum_add_distrib]; rw [show linearFace (G:=G) (x,q) B=crackle i j B x from (plot i j q.property x B).symm,PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro c _; simp only [crackle_ap,PiLp.add_apply,PiLp.sub_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]; unfold i j; ring

-- whole and seam ordinary products

def engine (p:Mark)(G:Gauge): Stamp G:= ∑ u:PlaqAxes, send p (fun x=> V3 G (x,u))
def localR (p:Mark)(v: Warp G):Stamp G:= ∑ j:Axis,∑ c:G.ColorIndex,send p (fun x=> chassis x j c*pulseR v x j c)
def shellK (p:Mark)(v: Warp G):Stamp G:= ∑ j:Axis,∑ i:Axis,∑ c:G.ColorIndex,send (sibling p i) (fun x=> harp (curlFee (x-step i) i j c).line *pulseR v x j c)

theorem ports (p:Mark)(v:Warp G) : part (G:=G) (grad v) (engine p G)= -(localR p v + shellK p v):=by
  apply same; intro A; unfold engine localR shellK; rw [_root_.map_neg,_root_.map_sum]; simp_rw [by_send]; let Q:=pit A; let B:=rLink v A; let f (i j:Axis)(c:G.ColorIndex)(z:Cover):ℂ:= ↑(crackle i j A z c); let g (j:Axis)(c:G.ColorIndex)(z:Cover):ℂ:= ↑(B (z,j) c)
  have he:(∑ u:PlaqAxes, Q (send p (fun x=> part (G:=G) (grad v) (V3 G (x,u)))))= -(∑ j:Axis,∑ i:Axis,∑ c:G.ColorIndex,send p (fun z=> f i j c z*(g j c (z+step i)-g j c z))):=by
    simp_rw [show ∀ (p:Mark)(f:Cover→Stamp G), Q (send p f) = send p (fun x=> Q (f x)) from fun p f=> by_send Q.toLinearMap p f, show ∀ q:Face ℤ,Q (part (G:=G) (grad v) (V3 G q))=-↑(inner ℝ (linearFace q A) (linearFace q B)) from fun q=>price_ward ..]
    simp_rw [send_many]; rw [← map_neg]; congr 1; funext x; rw [Finset.sum_neg_distrib,ticket_price, Finset.sum_comm]; rfl
  change Q _= -(Q (_+_)); rw [map_sum,map_add,he]; simp_rw [map_sum,show ∀ (p:Mark)(f:Cover→Stamp G), Q (send p f)=send p (fun x=> Q (f x)) from fun p f=>by_send Q.toLinearMap p f,map_mul, show ∀ i: Line G,Q (harp i) = ↑(probe i A) from fun i=> leg_test i A, show ∀ x j c,Q (pulseR v x j c)=g j c x from fun x j c=> pulse_at ..,curls_hit, contour,Finset.sum_add_distrib]
  congr 2; refine Finset.sum_congr rfl fun j _=>?_ ; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _=>?_; rw [send_many]; congr 1; funext x; rw [← Finset.sum_mul]; unfold f Q chassis; rw [leg_test, main_ap,← fit_value x (Scale.press A) j, Scale.job,Finset.sum_apply, WithLp.ofLp_sum,Finset.sum_apply, Complex.ofReal_sum]; congr 1; refine Finset.sum_congr rfl fun i _=>?_; exact (Complex.ofReal_sub _ _).symm
end YM.XSpace.Prelude
