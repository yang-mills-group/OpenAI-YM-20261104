import YM.Next.RANK.LoomBox
import YM.WilsonCoeffUV.Reclosure.Pricing
/-!
# Based path lift for *source*: independent legs
Spindle lemma linearized. Works on all positive periods at once, untouched
lifted paths. Cost polynomial range, only one face word element per lift term.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators
open Work.F03 Next.Rank
variable {G:Gauge}{n:Side}
section paths
open Spindle Work
variable {R:ℕ}
lemma close_box (x:Cover){n:ℕ}(h:size x≤n): x∈box n:=by
  have hx i:(x i).natAbs ≤n:= (Finset.single_le_sum (f:=fun j:Axis=> (x j).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans h
  exact box_test.mpr ⟨fun i=>by have hu:=hx i; omega,fun i=>by have hu:=hx i; omega⟩
lemma size_go (i:Axis): size (step i:Cover)=1:=by simp [size, apply_ite Int.natAbs]

def cusp (x:Cover):=size x+1
lemma patchP (x:Cover)(i:Axis): x+step i ∈ box (cusp x) := close_box _ ((size_add ..).trans (by rw [size_go]; rfl))
def turnPlan (G:Gauge)(x:Edge Cover) : Word (cusp x.1):= (rolled G x.1 x.2 (close_box _ (Nat.le_succ _)) (patchP x.1 x.2)).choose
lemma turn_bounds (G:Gauge)(x:Edge Cover): (turnPlan G x).length≤size x.1∧∀ U:CoverConfig G, central U x=played (used U) (turnPlan G x):=
  (rolled G x.1 x.2 (close_box _ (Nat.le_succ _)) (patchP x.1 x.2)).choose_spec

def curlP (p:Turn R): Slot:=⟨paths p.val.1,p.val.2⟩
lemma railC (p:Turn R): (curlP p).offset=p.val.1:=stops _
lemma reachC (p:Turn R): (curlP p).length≤4*R+4:=by unfold curlP Slot.length; rw [lengths]; exact Nat.add_le_add_right (bounded (faceOrigin p)) _
abbrev wordBand (G:Gauge)(x:Edge Cover):= Fin (turnPlan G x).length
def scoreP (u:Bool):ℝ:=if u then -1 else 1
@[simp] lemma sign_score (u:Bool): |scoreP u|=1:=by cases u<;>simp [scoreP]

def forestP (A:Link G n): Cover→ G.Color:= fun x => linkSum (collect G (arm G n 1 A)) 0 (paths x)
lemma gauge_growth (A:Link G n)(x:Cover) : ‖forestP A x‖≤ size x * ‖arm G n 1 A‖:=by
  let a:= arm G n 1 A
  have hx (w:Walk)(y:Site n): ‖linkSum (collect G a) y w‖ ≤ w.length * ‖a‖:= by
    induction w generalizing y with
    | nil=> simp [linkSum]
    | cons i u ih=>
       unfold linkSum; let Z:=collect G a (i.used y); apply (norm_add_le ..).trans (le_trans (add_le_add (show ‖(if i.neg then -Z else Z)‖ ≤ ‖a‖ from ?_) (ih _)) ?_); swap; · simp; linarith
       unfold Z collect; split<;>simpa only [norm_neg] using (norm_le_pi_norm a _)
  apply (hx (paths x) 0).trans_eq; rw [lengths]; rfl
-- rate statement from a rooted transport

def ledP (A:Link G n)(t:ℝ):CoverConfig G:=expandAt 0 (input G n (t • A))
lemma ledS (A:Link G n)(t)(z:Cover)(v): ledP A t (z,v)=(represent (t • arm G n 1 A)) (wrap n z,v):=by unfold ledP expandAt input; rw [add_zero,map_smul]
lemma ledZero (A:Link G n): ledP A 0=1:= by funext ⟨i,j⟩; rw [ledS,zero_smul,link_one]; rfl
lemma leaves_zero (A:Link G n)(x: Cover): leaves (ledP A 0) x=1:=by
  unfold leaves ledP; rw [travel_at,map_zero,zero_add,input,map_smul,zero_smul]; exact Push.stroll_zero ..
lemma leaves_rate (A:Link G n)(x:Cover): HasDerivAt (fun t:ℝ=> G.mat (leaves (ledP A t) x)) (G.colorMat (forestP A x)) 0 := by
  unfold leaves ledP forestP; simp_rw [travel_at,map_zero,zero_add,input,map_smul]; exact Push.travell ..
lemma ax_score (A:Link G n)(u:Cover)(i:Axis): HasDerivAt (fun t:ℝ=> G.mat (central (ledP A t) (u,i))) (G.colorMat (forestP A u + arm G n 1 A (wrap n u,coord i)-forestP A (u+step i))) 0:=by
   have h (t): central (ledP A t) (u,i)= leaves (ledP A t) u * represent (t • arm G n 1 A) (wrap n u,i) * (leaves (ledP A t) (u+step i))⁻¹:=by unfold central Lattice.gauge; rw [ledS]
   simp_rw [h,G.mat_mul,G.mat_inv]
   convert! (((leaves_rate A u).mul (represent_rate ..)).mul ((leaves_rate A (u+step i)).star)) using 1
   simp [leaves_zero,link_one,G.colorMat_skew,sub_eq_add_neg]
lemma prismRead (A:Link G n)(p:Turn R)(t): faceValue (ledP A t) p.val=faceValue (represent (t • arm G n 1 A)) (slotFace (curlP p) (0:Site n)) := by
   conv_lhs=> unfold faceValue ledP; rw [travel_at,input,map_smul];
   unfold faceValue slotFace; rw [railC]; rfl
lemma juk_score (A:Link G n)(p:Turn R): HasDerivAt (fun t:ℝ=> G.mat (used (ledP A t) p)) (G.colorMat (faceCurl (slotFace (curlP p) (0:Site n)) (arm G n 1 A))) 0:=by
   unfold used central; simp_rw [face_gauge, prismRead, G.mat_mul,G.mat_inv]
   have h:= leaves_rate A p.val.1
   convert! (((h.mul (face_deriv ..))).mul h.star) using 1
   simp only [Pi.mul_apply, leaves_zero, G.mat_one,G.colorMat_skew, star_one,one_mul,mul_one, zero_smul, show faceValue (represent (0:fieldDir G n 1)) (slotFace (curlP p) (0:Site n))= 1 from Push.stroll_zero ..]
   abel
lemma jub_zero (A:Link G n)(p:Turn R): used (ledP A 0) p=1:= by unfold used central; rw [face_gauge,prismRead]; simp only [leaves_zero,zero_smul,one_mul,inv_one,mul_one]; exact Push.stroll_zero ..
lemma play_zero (A:Link G n)(p:Word R): played (used (ledP A 0)) p=1:=by
   induction p with
   | nil=> simp [played]
   | cons i p ih=> rw [played,List.map_cons,List.prod_cons, jub_zero]; change _*played _ p=1; simp [ih]
lemma jig_score (A:Link G n)(p:Turn R × Bool): HasDerivAt (fun t:ℝ=> if p.2 then G.mat ((used (ledP A t) p.1)⁻¹) else G.mat (used (ledP A t) p.1)) (G.colorMat (scoreP p.2 • faceCurl (slotFace (curlP p.1) (0:Site n)) (arm G n 1 A))) 0:=by
    obtain ⟨p,_|_⟩:=p<;>simp only [Bool.false_eq_true,scoreP,↓reduceIte,one_smul,neg_smul,G.mat_inv,map_neg,←G.colorMat_skew]; exact juk_score ..; exact (juk_score ..).star
lemma puzzle (A:Link G n)(w:Word R): HasDerivAt (fun t:ℝ=> G.mat (played (used (ledP A t)) w)) (G.colorMat (∑ i:Fin w.length,scoreP (w.get i).2 • faceCurl (slotFace (curlP (w.get i).1) (0:Site n)) (arm G n 1 A))) 0:=by
   induction w with
   | nil=> simp [played]; exact hasDerivAt_const ..
   | cons i w ih=>
       let K (t):= if i.2 then G.mat ((used (ledP A t) i.1)⁻¹) else G.mat (used (ledP A t) i.1)
       have h : K 0=1:=by simp [K,jub_zero]
       have hf (t): G.mat (played (used (ledP A t)) (i::w))=K t* G.mat (played (used (ledP A t)) w):=by rw [played,List.map_cons,List.prod_cons,G.mat_mul]; unfold K; split<;>rfl
       simp_rw [hf]; change HasDerivAt (fun t=>K t * G.mat _) (G.colorMat (∑ j:Fin (w.length+1),_)) 0
       rw [Fin.sum_univ_succ]; convert! (jig_score A i).mul ih using 1; simp [jub_zero,play_zero]
-- search forest linear slot derivative result. leading map is orientation-neutral.
def bladeP {x}(j:wordBand G x) : Slot:= curlP ((turnPlan G x).get j).1
def glisten {x}(j:wordBand G x):= scoreP ((turnPlan G x).get j).2
lemma glow {x}(j:wordBand G x): ‖glisten j‖=1:= sign_score _
lemma glower {x}(j:wordBand G x): (bladeP j).length ≤ 4*cusp x.1+4:= reachC _
lemma worth_axis (A:Link G n)(x:Edge Cover) : ∑ j:wordBand G x, glisten j • faceCurl (slotFace (bladeP j) (0:Site n)) (arm G n 1 A) = forestP A x.1+ arm G n 1 A (wrap n x.1,coord x.2)-forestP A (x.1+step x.2) := by
    apply G.colorMat_injective
    have hx:= ax_score A x.1 x.2
    simp_rw [(turn_bounds G x).2] at hx; exact (puzzle A (turnPlan G x)).unique hx
end paths
end YM.WilsonCoeffUV.Mer.Rolls
