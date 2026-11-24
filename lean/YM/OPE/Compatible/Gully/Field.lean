import YM.OPE.Compatible.Gully.Rum
/-!
# Density matrix. Exact self-price under infinity Wick
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Nestle Balsam Port
open GaussianScore Libra WithLp RG Precision Votive
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}{U:Gloam}
structure Match (U:Gloam)(G:Gauge) where
    P:Pose
    sit:Crew U
    a:G.ColorIndex
def ps (x:Match U G)(i:ℕ)(H:Even (U.M i).val) := poseT H (x.sit.val i) x.a x.P
abbrev launchW (x y:Match U G)(hr:4≤r)(C:KernelChoices)(i:ℕ)(H:Even (U.M i).val):= (boost H (Train.top r) hr C).wick (ps x i H) (ps y i H)
def rootW (x y:Match U G):= if x.a=y.a ∧ x.sit=y.sit then zine y.P x.P.icicle else 0
lemma tip_twine (p:Pose)(s:Site n)(f:Axis→Site n→ℝ)(x:ℝ):tip p (fun i j=>x*f i j) s=x*tip p f s:= Eq.symm (show _ from act_tip ((x • LinearMap.id (R:=ℝ) (M:=ℝ)).toAddMonoidHom) _ _ _)
abbrev rolledW (x y:Match U G)(i:ℕ)(k:Kv):=tip y.P (fun a u=>paper (reed x.P k) a (decks k (x.sit.val i)) u) (y.sit.val i)
lemma launch_parts (x y: Match U G)(i:ℕ)(H:Even (U.M i).val)(hr:4≤r):launchW x y hr C i H= if x.a=y.a then ∑ j:Kv, torque x.P j * rolledW x y i j else 0:=by
    let W:= boost H (Train.top r) hr C (G:=G); let X:=W.inverse (ps x i H)
    let Y(a u):= Tags H y.a a u X
    have hp: poseT H (y.sit.val i) y.a y.P X = tip y.P Y (y.sit.val i):=by
        let A: Dual' (Libra.Keys G (Limb H)) →+ ℝ:= ⟨⟨(fun i=>i X),rfl⟩,fun a b=>rfl⟩; exact act_tip A _ _ _
    have hg(a u):= wickPose (C:=C) H (x.sit.val i) u a x.P x.a y.a hr; change poseT H _ _ _ X=_; rw [hp]; split
    next hh=> unfold Y X W ps; simp_rw [hg,if_pos hh]; erw [tip_sum]; refine Finset.sum_congr rfl (fun i' _=>?_); exact tip_twine ..
    next hh=> unfold Y X W ps;simp_rw [hg,if_neg hh]; exact tip_zero ..
def SpareW (x y:Crew U):=∀ j:Kv,j≠0→decks j (x.val 0) ≠ y.val 0
lemma spunC0 (x: Crew U)(h:∀ i,Even (U.M i).val): SpareW x x:=by
   intro j hj he; let n:= U.M 0; have hn:n.val/2 ≥1:=by obtain ⟨k,hk⟩:= h 0; have ht:0<n.val:=n.property; change n.val=k+k at hk; omega
   have hx:= deck_free j hj (x.val 0); rw [he,separation_self] at hx; exact (by unfold n at hn; omega)
lemma roll_zero (p:Pose): reed p 0=p ∧ torque p 0=1:=by
    have H(i:Axis):spotK 0 i=0:=by simp [spotK]
    have hp(l:List Axis): offsetK 0 l=0 ∧ trailK 0 l=1:=by induction l with
      | nil=>exact ⟨rfl,rfl⟩
      | cons a l ih=> rw [offsetK,H,trailK,ih.2, ih.1]; simp [omegaK]
    simp [reed,H,hp p.m,torque,omegaK]
lemma embark (H:∀ i,Even (U.M i).val)(x y:Match U G)(h:SpareW x.sit y.sit)(hr:4≤r): GammaSite U (x.P.heat+y.P.heat) (fun i=>launchW x y hr C i (H i)-rootW x y):=by
   simp_rw [launch_parts]; unfold rootW; by_cases ht:x.a=y.a; swap; · simp only [if_neg ht, if_neg (fun (hx:x.a=y.a ∧ x.sit=y.sit)=>ht hx.1),sub_self]; unfold GammaSite; dsimp only; simp only [mul_zero]; exact cleared_zero _
   simp only [ht,true_and,ite_true,eq_self]; let A:Finset Kv:= Finset.univ.erase 0; let G(j: Kv)(i:ℕ):=torque x.P j*rolledW x y i j; let w(_i:ℕ):= if x.sit=y.sit then zine y.P x.P.icicle else (0:ℝ); let d:=x.P.heat+y.P.heat; -- w unused i
   have he(j)(hp:j∈A): GammaSite U d (G j):=by
       let p:=reed x.P j; let z:Crew U:=⟨fun i=>decks j (x.sit.val i),orbitB0 U _ j H⟩
       have hz:z ≠ y.sit:= fun hh=>h j (Finset.mem_erase.mp hp).1 (show decks j (x.sit.val 0)=_ from congr_fun (congr_arg Subtype.val hh) 0)
       have hh:GammaSite U d (fun i=>rolledW x y i j):=prom z y.sit p y.P hz
       unfold GammaSite; convert! Cleared.pen (Cleared.always (x:=torque x.P j)) hh using 2 with i; change _*(torque _ _*_)= torque x.P j*(_*_);ring
   have hg:GammaSite U d (fun i=>G 0 i-w i):=by
       unfold G rolledW w; rw [roll_zero x.P |>.1,roll_zero x.P|>.2]; simp_rw [flats,one_mul]; split_ifs
       next ha=> have he(i):x.sit.val i= y.sit.val i:=congr_fun (congr_arg Subtype.val ha) i; simp_rw [he]; exact prom_same y.sit x.P y.P H
       next ha=> simp only [sub_zero]; simpa using! prom x.sit y.sit x.P y.P ha
   unfold GammaSite
   change Cleared U (fun i=>(U.h i^d)⁻¹*((∑ j,G j i)-w i))
   rw [show (fun i=>_)= (∑ j∈A, fun i:ℕ=>(U.h i^d)⁻¹*G j i)+(fun i:ℕ=>(U.h i^d)⁻¹*(G 0 i-w i)) from ?_ ]; exact (Cleared.tally _ _ he).fuse hg -- tally he type
   funext i; rw [Pi.add_apply,Finset.sum_apply,←Finset.mul_sum]; unfold A; rw [← Finset.sum_erase_add (s:=Finset.univ) (f:=fun j:Kv=>G j i) (a:=0) (by simp)]; ring
end YM.OPE.StageLight
