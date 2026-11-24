import YM.MS.Orbit.Roster
/-!
# Actual site cycle operations, including defect branch from image. No equivalence hypotheses. Bounds later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{P:Latch.Edge G}{F: Law G}{n:Side}
lemma φ_first (p:Cover)(x y:Site n): Φa p (x+y)=Φa p x * Φa p y:= Bloch.cell_add ..
lemma φ_start (p q:Cover)(x:Site n): Φa (p+q) x= Φa p x*Φa q x:= by simp only [φ_c, be, emb_add, payadd ]
abbrev Dph (b:Bool)(A B:Cover):= A+taste b B
lemma chase_pc (p:Cover)(b:Bool)(h:Speaks F): frame ( faceκ b n P ) (anchor G n p F)= anchor G n p ( Θ_pc b (σcap n) ( Dph b p p ) (ηbone b P) F ):= by
   funext w; rw [ on_frame ]; let q:= taste b p; rw [chase_now, point, Θ_pc, barkU]; simp_rw [Finset.sum_apply,diffPair_apply,Pi.smul_apply,smul_eq_mul,at_D, chase_now, compete _ _ _ _ h b, net_cons, Finset.mul_sum]; -- often need β
   refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun j _=>?_; simp only [Dph,← φ_c, φ_first, φ_start, φ_other ]; ring
lemma pc_bulk (h:Speaks F): frame ( mat n P ) (Bulk G n F)= Bulk G n (Θ_pc false (σcap n) 0 P F ):= by
   funext w; rw [show frame ( mat n P ) (Bulk G n F)= _ from on_frame (P:=P) false (Bulk G n F),bulkZ,point,Θ_pc, barkU]; simp_rw [Finset.sum_apply, diffPair_apply, Pi.smul_apply, smul_eq_mul, at_D, bulkZ ]; have hω(i j:BH G)(p:Site n):net ( (i,p)::(j,Omega _ false p)::w)=net w:= (by change p+(-p+_)=_; abel ); simp_rw [hω, compete _ _ _ _ h false ]; by_cases he:net w=0; swap; · simp [he]
   simp_rw [if_pos he, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun j _=>?_; change scaleZ n * P x j (Coord i)* _= _; rw [show be 0 (Coord i)=1 from (by simp [be, show embed 0=0 from (by ext; simp [embed])])]; ring
-- Pixel proof via junction. `$phase filter ℓ:` evaluated after q branch.
abbrev Tloc (n:Side)(a:Half): Cover:= Lattice.lift ( thin n a )
lemma fixed_c (z:Half)(x:Zone n): Φa ( Tloc n z ) x= Bloch.cell (thin n z) x:= by simp [Φa,Tloc]
lemma mark_branch (w:Legs (FixedMode G (periodN n)))(p:Zone n)(i j:BH G): net ((i,p)::(j,Omega _ true p)::w)= p+p+net w:= (add_assoc ..).symm
lemma image_bulk (n:Side)(h:Speaks F)(he:SpeaksK P): frame ( faceκ true (periodN n) P ) (Bulk G (periodN n) F)=∑ z:Half, anchor G (periodN n) (Tloc n z) (birth (ηbone true P) F):= by
   funext w; let N:= periodN n; rw [on_frame]; simp_rw [ Finset.sum_apply, diffPair_apply, Pi.smul_apply,smul_eq_mul, chase_now, point ]
   let v:=net w; let d(q:QP):=detach (ηbone true P) F ( stage w ) q; have hp:= junction v ( net (stage w) ) (θ_net w) ( detach_pin (picture he) h (x:=stage w) );
   simp_rw [ at_D, bulkZ, mark_branch, fixed_c, compete w _ _ _ h true ]; apply Eq.trans ?_ hp;
   refine Finset.sum_congr rfl (fun i hi=>?_ ); by_cases hz: i+i+net w=0; swap; · simp_rw [if_neg hz]; simp [v,hz]
   dsimp only [v] at *; simp_rw [ if_pos hz, detach ]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_ ; let K:=ηbone true P x y (Coord i); change scaleZ N*K*(brightness N *F ((x,Coord i)::(y,Coord i)::stage w)) = _; rw [mul_mul_mul_comm, lightW,one_mul ]; rfl
end YM.MS.Orbit
