import YM.XSpace.Embank

/-!
# Full compensated position limit at first perturbative order

Continue toward actual kcert scheme; intermediate, because `repair` not known to be
real or signed-equivariant on its finite parts and normalization conditions not imposed.
Scale positions have CLEARANCE explicitly even in coverage even if no support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Foundation
open Filter Set Function Lattice Chart2 Mu Trace Furlough JetGauge Stall Outline Shade Lows Drama Future Playpen
open scoped Topology BigOperators
variable {G:Gauge} (W:Initialize G) {I:Type} [DecidableEq I] {d:I→ℕ} (p:Form G d) (s:Finset I)(c:Shade.Cut) (a:ℝ) (x:I→Cover)

def bend := ∑ j∈s,LText W (s.erase j) p a x (x j) (base a^(d j) • rf W c (d j) a (p j))
def startup:= basic W s p a x - bend W p s c a x
private def city (o:PlaqAxes) := ∑' y:Cover,spill c s a x y * sends (y,o) (sess W s p a x)
lemma portion (j:I)(h:j∈s)(o:PlaqAxes): base a^(d j)* LText W (s.erase j) p a x (x j) (Shade.measure c a (Uptown.spirit (initial W j) (p j) o))=∑' y:Cover,pace c a (y-x j) * sends (y,o) (sess W s p a x):=by
  have he(y:Cover): base a^(d j)* LText W (s.erase j) p a x (x j) (Uptown.spirit (initial W j) (p j) o y)= sends (x j+y,o) (sess W s p a x):=by
    let S:=sess W (s.erase j) p a x; let F:= freeze (snaps W (p j) (x j) a); have hp : sess W s p a x=F*S:=(Finset.mul_prod_erase s _ h).symm
    unfold LText Uptown.spirit sends; rw [hp]; change _*E (Mu.root G) (freeze (Trace.volume _ (tie G _ _))*_) =_
    rw [← Mu.bring,out]; unfold F; rw [snaps,map_smul]; -- fix
    rw [← show V3 G (x j+y,o)= Trace.volume (x j) (V3 G (y,o)) from by rw [encoded (x j+y),encoded y,stroll], show ∀ q:Face ℤ,freeze (V3 G q)=V3 G q from fun q=> no_twin (by rw [gone,opens_V]), smul_mul_assoc,mul_smul_comm,map_smul]; let p':= freeze (slack W (x j) (p j)); change _* E (Mu.root G) (p'* _*S)= base a ^ (d j) * E (Mu.root G) (_*(p'*S)); rw [mul_comm p',mul_assoc (V3 ..)]
  rw [← Equiv.tsum_eq (Equiv.addLeft (x j))]; simp_rw [show ∀ y, (Equiv.addLeft (x j)) y=x j+y from fun _=>rfl,add_sub_cancel_left]
  rw [quick_sum,map_sum,Finset.mul_sum,tsum_eq_sum (s:=(outfit c a).support)]; refine Finset.sum_congr rfl fun y _=>?_ ; rw [map_smul,smul_eq_mul,mul_left_comm,he]
  intro i hi; rw [← outfit_eq,Finsupp.notMem_support_iff.mp hi,zero_mul]
lemma partitions (q: PlaqAxes): city W p s c a x q=(∑' y: Cover, sends (y,q) (sess W s p a x))-∑ i∈s, base a^(d i)*LText W (s.erase i) p a x (x i) (measure c a (Uptown.spirit (initial W i) (p i) q)):=by
  let f y:= sends (y,q) (sess W s p a x); let g i (y:Cover):=pace c a (y-x i)*f y
  have hx : ∀ i:I,Summable (g i):=by
    intro i; apply (Equiv.addRight (x i)).summable_iff.mp; apply summable_of_ne_finset_zero (s:=(outfit c a).support); intro y hy; unfold g comp; rw [show (Equiv.addRight (x i)) y=y+x i from rfl]; dsimp only; rw [add_sub_cancel_right, ← outfit_eq,Finsupp.notMem_support_iff.mp hy,zero_mul]
  unfold city; simp_rw [spill,sub_mul,one_mul,Finset.sum_mul]; rw [Summable.tsum_sub (f:=f) (g:=fun y=>∑ i∈s,g i y) (sweeping ..) (summable_sum fun i _=> hx i), (hasSum_sum (a:=fun i=>∑' y,g i y) (f:=g) (s:=s) (fun i _=>(hx i).hasSum)).tsum_eq]; congr 1; exact Finset.sum_congr rfl fun i hi=>(portion W p s c a x i hi q).symm
lemma cover_cost : startup W p s c a x= (∑ i∈s,LText W (s.erase i) p a x (x i) (Chapter.compCost c W (p i) a))-∑ i:PlaqAxes,city W p s c a x i:=by
  let f i := LText W (s.erase i) p a x (x i); let K:= base a
  have he i: f i (Chapter.compCost c W (p i) a)= K^(d i)* f i (Prelude.mark1 (initial W i (d:=d)) (p i))-(∑ q:PlaqAxes,K^(d i)*f i (measure c a (Uptown.spirit (initial W i) (p i) q)))- f i ( K^(d i) • rf W c (d i) a (p i)):=by
    change f i (K^d i • (Prelude.fuse (initial W (d:=d) i) (p i) c a- rf W c _ _ (p i)))=_; rw [Uptown.drama,smul_sub,smul_sub,map_sub,map_sub,map_smul,Finset.smul_sum,map_sum]; simp only [map_smul,smul_eq_mul]
  unfold startup bend; rw [exposure]; unfold hotspot; simp_rw [partitions]; change _=(∑ i∈s,f i _)-∑ i:PlaqAxes,(_-∑ j∈s,K^d j*f j _); simp_rw [he,Finset.sum_sub_distrib,Finset.sum_comm (s:=s)]; unfold K f; abel
lemma startup_plus (v:Cover): startup W p s c a (fun i=>v+x i)=startup W p s c a x:=by unfold startup bend; rw [whole_plus]; simp_rw [text_plus W _ _ a x v]

-- deliver full kernel-frontage theorem in these observation units and for these regulators of the UV
variable {ι:Type}{L:Filter ι}[L.IsCountablyGenerated]{α:ι→ℝ}{x:ι→I→Cover}{w:I→E4}
variable (h: Tendsto α L (𝓝 0))(S:∀ᶠ i in L,0<α i)(H: Poses L α (fun i t=> x t i) w s)(he:Cleared c w s)
private lemma text0 (v:Stamp G): Trace.volume (G:=G) (0: Cover) v=v:= same fun A=>by rw [ting,show zone 0 A=A from funext fun i=>by simp [zone_ap]]
include h S H he
theorem compensation : Likely L fun t=> startup W p s c (α t) (x t):=by
  let F i t:= x t i; let v i t:= snaps W (p i) (F i t) (α t); have ht (p:I): ∀ (z:ι→Cover)(u:On.Grade G (d p)), Records α L z (fun i=> snaps W u (z i) (α i)):=fun z u=> Records.program z α (status (W.surveys _) u)
  simp_rw [cover_cost]; apply Likely.sub _ _
  · refine Likely.sum _ _ fun i hi=>?_ ; let T t:= x t i; let w' j:= w j-w i; let x' j t:= x t j-T t; let s':= s.erase i; let Q t:= Chapter.compCost c W (p i) (α t); let B j t:= snaps W (p j) (x' j t) (α t)
    have h' : Poses L α x' w' s':=⟨fun j hj=> fence L _ _ (H.payment j (Finset.mem_of_mem_erase hj)) (H.payment i hi),fun j hj k hk e=> H.ends (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) (sub_left_inj.mp e)⟩
    have hx:= reward W (p i) c h S h' (fun j hj=> he j (Finset.mem_of_mem_erase hj) i hi (Finset.mem_erase.mp hj).1) B (fun _ _=> ht ..); apply hx.congr
    filter_upwards with j; change E (Mu.root G) (freeze _ * _) = LText W s' p (α j) _ (T j) (Q j); let x₀ k:=x' k j; conv_rhs=> rw [show x j=(fun k=> T j+x₀ k) from funext fun k=>by unfold x₀ x'; abel]
    have K:= text_plus W s' p (α j) x₀ (T j) 0 (Q j); rw [add_zero] at K; rw [K]; change _= E (Mu.root G) (freeze (Trace.volume 0 (Q j)) * sess W s' p (α j) x₀); rw [text0];rfl
  exact Likely.sum _ _ fun i _=>(ticket_out c H h S i he v (fun j _=> ht j _ _)).2
end YM.XSpace.Foundation
