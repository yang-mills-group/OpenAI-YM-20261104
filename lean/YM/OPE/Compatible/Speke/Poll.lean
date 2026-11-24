import YM.OPE.Compatible.Speke.Rime
/-!
# The field excited around each distinct pose
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
variable {U:Gloam}{n:Side}{d r s:ℝ}{K:ℕ→ℕ}
-- Incoming line.From one image. Includes possible tie translations.
abbrev paper (p:Pose)(i:Axis)(b k:Site n):ℝ:=p.Lck (fun i=>mildX (i::p.m) (b-k+wrap n p.x)) i
def Candidate (U:Gloam):=Axis→ (i:ℕ)→ Site (U.M i)→ℝ
def vote (p:Pose)(x:Crew U):Candidate U:=fun i j k=> paper p i (x.val j) k
def peekX (z:Crew U)(x:Candidate U):Panels:=fun a i v=>x a i (rumB z i v)
lemma cop (H:∀ᶠ i in atTop,Even (U.M i).val)(z:Crew U) (p:Pose)(x:Crew U) :∃ d>0, Cohort U d (peekX z (vote p x)) (p.heat+1):=by
   by_cases he:x=z
   · subst x; refine ⟨1/2,by norm_num, Or.inr ⟨SinB p, p.cuff (fun D=>flood D U), ?_, Or.inr ⟨p,rfl,rfl⟩,Or.inl (p.cuff_pin H)⟩ ⟩
     funext a i v; have hx: z.val i - rumB z i v + wrap _ p.x=wrap _ (v+p.x):=by unfold rumB;rw [map_add]; abel
     unfold peekX vote paper Pose.Lck; rw [hx]; unfold SinB Pose.icicle Pose.ray Pose.Lck; -- RHS cuff.p.Cuff_tray private unfold via dsimp
     change _=( (if a=p.b then hull (p.a::p.m) (v+p.x) else 0)-(if a=p.a then hull (p.b::p.m) (v+p.x) else 0) ) + (((if a=p.b then shutter p.x (flood (p.a::p.m) U) else 0)-(if a=p.a then shutter p.x (flood (p.b::p.m) U) else 0)) i v); split_ifs<;> simp only [Pi.sub_apply,flood,shutter,seam,Pi.zero_apply] <;> ring
   let d:=seaRise U (x.val-z.val) 0; have hh:(x.val-z.val) 0≠0:=fun hh=> he (drum _ _ (sub_eq_zero.mp hh)); refine ⟨d,sea_pos hh, Or.inl (Or.inl ?_)⟩
   have hp(a i v): x.val i-rumB z i v+wrap _ a= (x.val-z.val) i + wrap _ (v+a):=by unfold rumB; rw [map_add,Pi.sub_apply]; abel
   rw [show peekX z (vote p x)=p.cuff (fun D=> ebb D U (x.val-z.val)) from ?_]; exact p.cuff_far (fdroon x.property z.property) hh
   funext a i v; unfold peekX vote paper Pose.Lck; rw [hp]; change _= (((if a=p.b then shutter p.x (ebb (p.a::p.m) U (x.val-z.val)) else 0)-(if a=p.a then shutter p.x (ebb (p.b::p.m) U (x.val-z.val)) else 0)) i v); split_ifs <;> first|rfl
-- runway supplies at complement
lemma wanted (h:Crown U K)(x:Crew U)(y: Cover)(l:List Axis):∃ C≥0,∀ᶠ i in atTop,∀ b∉ rush K x i,‖mildX l (x.val i-b+wrap _ y)‖ ≤ C*U.h i^(l.length+2):=by
   obtain ⟨r,hr,H⟩:= behind h x; obtain ⟨C,hC,M,hv⟩:= roof_peck (r/2) (half_pos hr) l; refine ⟨C,hC,?_⟩; filter_upwards [U.sides.eventually (eventually_ge_atTop M),H,(U.h_null.mul_const (size y:ℝ)).eventually (ge_mem_nhds (show 0*(size y:ℝ)<r/2 by rw [zero_mul];exact half_pos hr))] with i hi hx ht b hh; let t:= x.val i-b; let u:=t+wrap _ y
   apply hv _ hi; have he: pdist t≤ pdist u+size y:=by
         have he:=pdist_triangle u (-wrap _ y); rw [show u+ -wrap _ y=t from add_neg_cancel_right .., pdist_neg] at he; exact he.trans (Nat.add_le_add_left (Next.Free.within_size ..) _)
   have hp:= hx b hh; have hz:= U.h_pos i; change r≤ (pdist t:ℝ)*U.h i at hp
   change r/2≤ (pdist u:ℝ)*U.h i; have hV:=mul_le_mul_of_nonneg_left (show (pdist t:ℝ) ≤ (pdist u+size y:ℝ) by exact_mod_cast he) hz.le; linarith only [ht,hV,hp]
lemma Lck_wallet (p:Pose)(f:Axis→ℝ)(a):‖p.Lck f a‖ ≤ ‖f p.a‖+‖f p.b‖:=by unfold Pose.Lck; refine (norm_sub_le ..).trans (add_le_add ?_ ?_) <;> split <;> first|rfl|simp
lemma wanted_p (h:Crown U K)(x:Crew U)(p:Pose)(w:Cover)(a:Axis) :∃ C≥0,∀ᶠ i in atTop,∀ b∉ rush K x i, ‖vote p x a i (b+wrap _ w)‖ ≤ C*U.h i^(p.heat+1):=by
   obtain ⟨C,hC,L⟩:=wanted h x (p.x-w) (p.a::p.m); obtain ⟨B,hB,H⟩:=wanted h x (p.x-w) (p.b::p.m); refine ⟨C+B,by positivity,?_⟩; filter_upwards [L,H] with i hi hx b hh; unfold vote paper; rw [show x.val i-(b+wrap _ w)+wrap _ p.x=x.val i-b+wrap _ (p.x-w) from by rw [map_sub]; abel]; grw [Lck_wallet]; rw [add_mul]; exact add_le_add (hi _ hh) (hx _ hh)
lemma want_step (h:Crown U K)(x:Crew U)(p:Pose)(a b':Axis):∃ C≥0,∀ᶠ i in atTop,∀ b∉ rush K x i,
    ‖vote p x a i b -vote p x a i (b+step b')‖ ≤ C*U.h i^(p.heat+1+1):=by
   obtain ⟨C,hC,L⟩:=wanted h x (p.x-step b') (b'::p.a::p.m); obtain ⟨B,hB,H⟩:=wanted h x (p.x-step b') (b'::p.b::p.m); refine ⟨C+B,by positivity,?_⟩; filter_upwards [L,H] with i hi hx b hh
   let G(j):= mildX (b'::j::p.m) (x.val i-b+wrap _ (p.x-step b')); have he:vote p x a i b-vote p x a i (b+step b')=p.Lck G a:=by unfold vote paper G Pose.Lck; simp_rw [mild_more,map_sub,wrap_step,show x.val i-b+(wrap (U.M i) p.x-step b')+step b'=x.val i-b+wrap _ p.x from by abel, show x.val i-b+(wrap _ p.x-step b')=x.val i-(b+step b')+wrap _ p.x from by abel]; split_ifs <;> ring
   rw [he]; grw [Lck_wallet]; rw [add_mul]; exact add_le_add (hi b hh) (hx b hh)
end YM.OPE.Nestle
