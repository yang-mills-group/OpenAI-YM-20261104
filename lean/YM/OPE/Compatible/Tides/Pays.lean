import YM.OPE.Compatible.Tides.Tone
import YM.OPE.Compatible.Tides.Lobe
/-!
# germ on wings. Upper marks all offsets and tail shelves
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{d:ℝ}{g h:ℕ→ Cover→ℝ}{k j:ℕ}
structure InkCost (U:Gloam)(d:ℝ)(k:ℕ)(g:ℕ→Cover→ℝ):Prop where
   inside : 0<d
   remit (x:Cover): Cleared U (fun i=>(U.h i^k)⁻¹*g i x)
   near (r:ℝ) (hr:r<d):∃ C≥0,∀ᶠ i in atTop,∀ x:Cover,U.h i * size x≤ r→ ‖g i x‖ ≤ C*U.h i^k
lemma InkCost.sell (hp:InkCost U d k g)(x:Cover):∃ p,Bloom U k (fun i=> g i x) p:=fromCore (hp.remit x)
def slit (U:Gloam)(k:ℕ)(g:ℕ→Cover→ℝ):ℝ:=if h:∃ p,Bloom U k (fun i=>g i 0) p then Classical.choose h else 0
lemma InkCost.slit (hp:InkCost U d k g): Bloom U k (fun i=>g i 0) (slit U k g):=by unfold Balsam.slit;rw [dif_pos (hp.sell 0)]; exact Classical.choose_spec _
lemma InkCost.glue (hf:InkCost U d k g)(hp:InkCost U d k h): InkCost U d k (g+h):=by
   constructor
   · exact hp.inside
   · intro x; convert! (hf.remit x).fuse (hp.remit x) using 2 with i; simp [Pi.add_apply,mul_add]
   intro r hr; obtain ⟨C,hC,H⟩:=hf.near r hr; obtain ⟨B,hB,L⟩:=hp.near r hr; refine ⟨C+B,by positivity,?_⟩; filter_upwards [L,H] with i hi hi' x hx; rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (hi' _ hx) (hi _ hx))
lemma InkCost.mool (hf:InkCost U d k g)(hp:InkCost U d j h):InkCost U d (k+j) (g*h):=by
   refine ⟨hp.inside,fun x=>?_,fun r hr=>?_⟩
   · obtain ⟨p,H⟩:=hf.sell x; obtain ⟨q,G⟩:=hp.sell x; exact ((H.pen G).2.1)
   obtain ⟨C,hC,H⟩:= hf.near r hr; obtain ⟨B,hB,L⟩:=hp.near r hr; refine ⟨C*B,by positivity,?_⟩; filter_upwards [L,H] with i hi hi' x hx; simp only [Pi.mul_apply,norm_mul]; have he:=U.h_pos i; refine (mul_le_mul (hi' _ hx) (hi _ hx) (norm_nonneg _) (by positivity)).trans (le_of_eq ?_); rw [pow_add]; ring
def shutter (a:Cover)(g:ℕ→Cover→ℝ)(i x):=g i (x+a)
lemma InkCost.pass (hf:InkCost U d k g)(x:Cover): InkCost U d k (shutter x g):=by
   refine ⟨hf.inside,fun p=>hf.remit _,fun r hr=>?_⟩
   obtain ⟨R,hR,hr⟩:= exists_between hr; obtain ⟨C,hC,H⟩:=hf.near R hr; refine ⟨C,hC,?_⟩; filter_upwards [H,(U.h_null.mul_const (size x:ℝ)).eventually (ge_mem_nhds (show 0*(size x:ℝ)< R-r from by linarith))] with i hi hh y hx; apply hi (y+x); have eh:=U.h_pos i; grw [size_add]; push_cast; linarith -- positivity
abbrev stalkP (l:List Axis)(g:ℕ→Cover→ℝ)(i:ℕ): Cover→ℝ:= dvol l (g i)
def Port (U:Gloam)(d:ℝ)(k:ℕ)(g:ℕ→Cover→ℝ):Prop:=∀ l:List Axis,InkCost U d (k+l.length) (stalkP l g)
def smear (i:Axis)(g:ℕ→Cover→ℝ)(j):=numDiff i (g j)
lemma streak (l:List Axis)(g:ℕ→Cover→ℝ)(a:Axis): stalkP l (smear a g)=stalkP (a::l) g:=funext fun _=>(rotate_tail l a _).symm
lemma Port.lo (hf:Port U d k g): InkCost U d k g:=hf []
lemma Port.split (hf:Port U d k g)(a:Axis):Port U d (k+1) (smear a g):=by
   intro l; rw [streak, show k+1+l.length=k+(a::l).length from by simp;omega]; exact hf _
lemma Port.glue (hf:Port U d k g)(hp:Port U d k h):Port U d k (g+h):=by
   intro l; rw [show stalkP l (g+h)=stalkP l g+stalkP l h from funext fun i=>funext fun x=> run_add ..]; exact (hf _).glue (hp _)
lemma Port.pass (hf:Port U d k g)(x:Cover):Port U d k (shutter x g):=by
   have he(l:List Axis)(g:ℕ→Cover→ℝ):stalkP l (shutter x g)=shutter x (stalkP l g):=by
      induction l generalizing g with
      | nil=> rfl
      | cons a l ih=>
        rw [← streak,show smear a (shutter x g)= shutter x (smear a g) from ?_]; rw [ih,streak]
        funext i z; unfold smear numDiff shutter; rw [add_right_comm z]
   intro l; rw [he]; exact (hf _).pass _
lemma Port.mool (hf:Port U d k g)(hp:Port U d j h):Port U d (k+j) (g*h):=by
   intro l; induction l generalizing k j g h with
   | nil=> exact hf.lo.mool hp.lo
   | cons i l ih=>
     rw [← streak]; let x:= step i (S:=ℤ) -- parse
     let L:=shutter x h; let H:=smear i h; let Q:=smear i g; let F:=Q*L
     rw [show smear i (g*h)=Q*L+g*H from funext fun j=>funext fun a=>by change g j (a+x)*h j (a+x)-g j a*h j a=(g j (a+x)-g j a)*h j (a+x)+g j a*(h j (a+x)-h j a);ring,show stalkP l (Q*L+g*H)= stalkP l F+stalkP l (g*H) from funext fun j=>funext fun a=>run_add ..,show k+j+(i::l).length=k+(j+1)+l.length from by simp; omega]; apply InkCost.glue _ (ih hf (hp.split i)); rw [show k+(j+1)=k+1+j from by omega]; exact ih (hf.split i) (hp.pass x)
lemma hardly (hp:InkCost U d k g){ε:ℝ}(hh:0<ε)(hr:ε≤d): InkCost U ε k g:=⟨hh,hp.remit,fun _ hu=> hp.near _ (lt_of_lt_of_le hu hr)⟩
lemma Port.slice (hp:Port U d k g){ε:ℝ}(hh:0<ε)(hr:ε≤d):Port U ε k g:=fun l=> hardly (hp l) hh hr
end YM.OPE.Balsam
