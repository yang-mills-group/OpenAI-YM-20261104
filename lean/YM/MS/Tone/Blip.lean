import YangMills.WilsonProof.NativeSupport.YM.MS.Tone.Beat
/-!
# Symbol evaluation of cylinder operators

Planes include their link shift not factors of V_Q. Constant `coin`. Master roots
 uses ordinary charge part with conservation. Rank unbounded local. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Bare Focus Landau Momentum Paint
open scoped Topology ContDiff
variable {G:Gauge} {A P:Type}
local notation "W" => Dot G Cover
local notation "E" => LightMode G Cover
local notation "B" => Branch G Axis
local notation "V" => LightMode G QP

def bornv (v:E): QP:= embed v.2+offset v.1.1
def paywave (p:V)(x:E): ℂ:= (way id p.1 x.1:ℂ)*bill p.2 (bornv x)
def run : W →ₗ[ℂ] Film G QP:= shade paywave
lemma in_light (v:V)(x:E)(h:paywave v x≠0): v.1=x.1:= Classical.byContradiction fun he=> h (by rw [paywave,need id (show v.1≠id _ from he),zero_mul])
lemma tied : Tie Draft.DotFlip Draft.DotFlip (paywave (G:=G)):= fun i j h=> show parity i.1=parity j.1 from (congr_arg parity (in_light j i h)).symm
lemma wave_cost (f g:W): run (couple Draft.DotFlip f g)=product Draft.DotFlip (run f) (run g):= tied.prod f g
lemma run_twist (b:Bool)(f:W): run (twisted Draft.DotFlip b f)=sign Draft.DotFlip b (run f):= tied.commute ..
@[simp] lemma pw (i:B)(x q): paywave (i,q) (i,x)=bill q (embed x+offset i.1):= by unfold paywave; rw [show way id i i=(1:ℂ) from only id i]; simp [bornv]
lemma tips (F:W){s:Finset Cover}(h:BoundBy (s:Set Cover) F)(q:QP)(a:B): Koszul.D (a,q) (run F) = ∑ x∈s,bill q (bornv (a,x)) • run (enter (a,x) F):= by
    change D _ (shade paywave F)=_
    rw [block F h paywave in_light (a,q)]; simp only [pw]; rfl
lemma grows (F:W){s:Finset Cover}(h:BoundBy (s:Set Cover) F)(q:V)(w:List V): run F (q::w)=∑ x∈s,bill q.2 (bornv (q.1,x)) * run (enter (q.1,x) F) w:= by
   rcases q with ⟨a,Q⟩; rw [D_eval _ (run F),tips F h,Finset.sum_apply]; rfl

lemma sway {T' U':V→E→ℂ}(z:V→ℂ)(F:Dot G Cover)(h:∀ i j,T' i j=z i*U' i j)(l:List V): shade T' F l= (l.map z).prod*shade U' F l:= by
    induction l generalizing F with| nil=> simp| cons i l ih=> obtain ⟨s,hs⟩:=fromCyl F; simp only [deriv_lum T' i F hs, h, ih, List.map_cons,List.prod_cons,deriv_lum U' i F hs,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma movement (F:W)(x:Cover)(l:List V): run (Lab.Shift x F) l=bill (net l) (embed x)*run F l:=by
   unfold run Lab.Shift transport; rw [study];
   let z:V→ℂ:=fun i=>bill i.2 (embed x)
   have he i j : paywave i (post (fun y:Cover=>x+y) j) = z i * paywave i j := by unfold paywave bornv; simp only [post, emb_add,add_assoc, rightadd,z, mul_left_comm (bill _ (embed x))]
   have hz : (l.map z).prod= bill (net l) (embed x):= by induction l with| nil=> exact (pay0 _).symm| cons i l ih=> simp [z] at *; rw [ih,payadd] -- lint
   rw [sway z F he,hz] -- unused binder axes
-- also joint shifts alias suppression

def veil (q: Cover)(i:B):ℂ:= bill (Tone.rep q) (offset i.1)
lemma consensual (F:W)(p:QP)(i:B)(q:Cover): D (i,p+rep q) (run F)= veil q i • D (i,p) (run F):= by
   obtain ⟨s,hs⟩:= obliges F; simp_rw [tips F hs, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [payadd,smul_smul]; unfold bornv; rw [rightadd (Tone.rep q),reciprocal,one_mul]; simp [mul_comm,veil]
lemma oneRank {F:W}{v:ℤ}(h:Book.Limit F.val v): Book.Limit (run F) v:= Book.Limit.shades F h _
lemma grade (n:ℤ)(F:W): run (Book.model n F)=Book.mask n (run F):= Book.mod_ink ..
lemma pulse (q:V)(x:E): run (Cylinder.single x) [q]=paywave q x:= Cylinder.name ..
end YM.MS.Tone
