import YM.RG05Readout.Harvest.Report
import YM.RG05Readout.Halls.Gable
/-!
# Field valuation linear terms. Restore weights/factors of measuring master
 at cutoff relative b.Vacancy.Power only.After all transfer.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k D:ℕ}{e:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A!"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "P"=> Bin G (C.side N p)
local notation "F₁"=> Site (C.side (n+1) p)
section crop
variable (z:ℂ) (S: Emblems C d)(v:Palette C d)
local notation "Y"=> precinct C p N d v
lemma precinct_t : timely (precinct C p N d v):=by
    intro f; rw [show precinct C p N d v f=clinic C p N d v N 0 t! f from ?_]; exact clinic_cut ..
    unfold clinic uniform; rw [dif_pos le_rfl,crops_head,Records.like_embed,stepid]
lemma precinct_zero : precinct C p N d 0=0:=by funext f; unfold precinct entrance; let L:= Mark C d; change (∑ i:L,_)=0; exact Finset.sum_eq_zero fun i _=>by rw [show val 0 i=0 from rfl,zero_smul]
lemma precinct_scale : precinct C p N d (z • v)= z • (precinct C p N d v):=by funext f; change _= z • (precinct C p N d v f); unfold precinct entrance; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=>mul_smul ..
lemma precinct_linear (q:Palette C d): precinct C p N d (v+q)= (precinct C p N d v)+(precinct C p N d q):=by
    funext f; change _=precinct C p N d v f+precinct C p N d q f -- placeholders update
    unfold precinct entrance; rw [←Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>add_smul ..
variable (hn:n+1 ≤ N) (F:Bin G (C.side N p))(g:Body)
local notation "η"=> n+1
lemma crop_extend (he:b ≤ m) (hm:m ≤ N): crops C m p N d hm (crops C N p N d le_rfl F m hm) b he = crops C N p N d le_rfl F b (he.trans hm):=by
   induction he using Nat.decreasingInduction with
   | self=>rw [crops_head]
   | of_succ i hi ih=> rw [crops_step _ _ hi, ih,crops_step _ _ (hi.trans_le hm)] -- placeholder
lemma crops_linear (he:n ≤ m)(hm:m ≤ N)(q:P): crops C m p N d hm (F+q) n he=crops C m p N d hm F n he+crops C m p N d hm q n he:=by
   funext g; rw [awaken hm (F+q) _ he]; simp only [Pi.add_apply,awaken hm F _ he,awaken hm q _ he]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ;
   change ratioX (Λ he p) d • stepUp t! _ (_+_)=_ ; rw [show stepUp t! _ (_+_)=_ + _ from rfl,smul_add];rfl -- fix helper
lemma crops_zero (he:n ≤ m)(hm:m≤ N): crops C m p N d hm 0 n he=0:=by funext f; rw [awaken]; exact Finset.sum_eq_zero (fun i _=> smul_zero _)
lemma crops_scale (he:n ≤ m)(hm:m≤N): crops C m p N d hm (z • F) n he= z • (crops C m p N d hm F n he):=by
    funext f; rw [awaken hm (z • F) _ he, Pi.smul_apply,awaken hm F _ he,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; let l:= Λ he p; let q:=F (feeR l i f); let a:=(Λ hm p).embed (l.assemble (0,i)); change ratioX l d • stepUp t! a (z • q)= _ ;rw [Records.rot_scalar]; exact smul_comm ..
lemma uniform_add (F:P)(R:P)(he:i ≤ n)(hn:n≤N) (z:Site (C.side i p)) : uniform C n p N d hn (F+R) i z t! g=uniform C n p N d hn F i z t! g+uniform C n p N d hn R i z t! g:=by unfold uniform; simp_rw [dif_pos he, crops_linear F he hn R]; rfl
lemma uniform_s (F:P)(he:i ≤ n)(hn:n ≤N)(u:Site (C.side i p)): uniform C n p N d hn (z • F) i u t! g=z • uniform C n p N d hn F i u t! g:=by unfold uniform; rw [dif_pos he, dif_pos he,crops_scale z F he hn,Pi.smul_apply,Records.rot_scalar]; rfl
lemma uniform_zero (he:i ≤ n)(hn:n ≤ N)(u:Site (C.side i p)): uniform C n p N d hn 0 i u t! g=0:=by simpa only [smul_zero,zero_smul] using uniform_s (d:=d) 0 g 0 he hn u
lemma field_translate (q:Body): fieldC C m N p d (z • v) q=z • fieldC C m N p d v q:=by
   unfold fieldC; rw [smul_comm z]; apply congr_arg (gate C m N d • ·); rw [Finset.smul_sum]
   refine Finset.sum_congr rfl (fun i _=>?_); let f':=restricted C N p i q; rw [show entrance C d N p (z • v) 0 f'= z • entrance C d N p v 0 f' from congr_fun (precinct_scale z v) f',Records.rot_scalar];rfl
local notation "P!'"=> C.side b p
variable (D₀:E4 → ℝ)
section
variable {S}
lemma return_weight (hv: b ≤ m)(f:Body)(he:m ≤ N) {R:ℝ}(hf: ∀ x∈tsupport f.val,‖x‖≤R)(hR:R+A! b*3< C.S.radius p) :
   (A! b:ℂ)^4 • gathered C m N p d he (crops C N p N d le_rfl Y m he) b f= fieldC C b N p d v f:= by
   rw [show gathered C m N p d he _ b f=gathered C N N p d le_rfl Y b f from ?_, mass le_rfl Y (precinct_null v) f hf (hv.trans he) hR]; -- edit
   · unfold fieldC; simp_rw [Records.like_embed]; rw [Finset.smul_sum]; symm;rw [Finset.smul_sum]; refine Finset.sum_congr rfl (fun i _=> ?_); rw [smul_smul]
     apply congr_arg (· • _); let r:=(Λ (hv.trans he) p); rw [money (p:=p) (b:=b) (hv.trans he)];
     unfold gate; rw [div_self,one_pow,mul_one]; exact Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'
   unfold gathered; apply Finset.sum_congr rfl; intro i _; unfold uniform; rw [dif_pos hv,dif_pos (hv.trans he), crop_extend]
end
end crop
end YM.RG05Readout.Harvest
