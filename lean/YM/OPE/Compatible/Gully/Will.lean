import YM.OPE.Compatible.Speke.Char
import YM.OPE.Compatible.Gully.Bean
/-!
# Stencil on every orbit. Transform charged roots
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch Further.FreeCovariance.KP MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Nestle Balsam Weir
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
def colK (k:Kv)(n:Side): Cover:= fun i=> if moveK k i then ((n.val/2:ℕ):ℤ) else 0
lemma colA (k:Kv)(n:Side): offset k n=wrap n (colK k n):=by funext i; change ite .. = (( (colK k n i:ℤ)): Per n); unfold colK; split_ifs<;> simp only [Int.cast_zero,Int.cast_natCast]
lemma orbitD (g:Ratio n m)(h:Even n.val)(k:Kv)(x:Site n): g.embed (decks k x)=decks k (g.embed x):=by
   simp_rw [decks,affine,← g.root_embed,map_add, g.root_embed,g.signed,colA, g.embed_wrap]; congr 2; ext i; simp only [Pi.smul_apply,colK]; split<;> rename_i hx
   · rw [nsmul_eq_mul]; obtain ⟨p,hp⟩:=h; have ht:m.val/2=p*g.count.val:=by rw [g.exact_size,hp, ← two_mul, mul_assoc]; omega
     rw [ht,hp]; rw [show (p+p)/2=p from by omega];push_cast; ring
   simp
lemma orbitB0 (U:Gloam)(b:Crew U)(k:Kv)(h:∀ i,Even (U.M i).val): Drone U (fun i=>decks k (b.val i)):=fun i=>by dsimp only; rw [b.property i,orbitD _ (h i)]
def omegaK (k:Kv)(a:Axis):ℝ:=if (axisK k).flip a then -1 else 1
def spotK (k:Kv)(a:Axis): Cover:=if (axisK k).flip a then -step a else 0
lemma ferry_at (k:Kv)(x:Site n)(a:Axis): ferry k (x,a)=(decks k x+wrap n (spotK k a),a):=by unfold ferry Step.used spotK; simp only [Step.rotate, posDir,axis_pin,Bool.false_xor]; split_ifs <;>simp [sub_eq_add_neg]
lemma deck_step (k:Kv)(x:Site n)(a:Axis): decks k (x+step a)=decks k x+(if (axisK k).flip a then -step a else step a):=by
    simpa only [Step.vec_pos, Step.rotate, posDir, axis_pin,Bool.false_xor,Step.vec,Bool.false_eq_true,if_false] using decks_walk k x (posDir a)
def trailK (k:Kv): List Axis→ ℝ | []=>1 | i::l=> omegaK k i*trailK k l
def offsetK (k:Kv) : List Axis→Cover | []=>0 | i::l=> spotK k i+offsetK k l
variable {V:Type*}[AddCommGroup V]
def fwd (a:Axis)(f:Site n→V)(x:Site n):=f (x+step a)-f x
def Knot (l:List Axis)(f:Site n→V):=l.foldr fwd f
def tip (p: Pose)(v: Axis→Site n→V)(x:Site n):V:= Knot p.m (fwd p.a (v p.b)-fwd p.b (v p.a)) (x+wrap _ p.x)
def reed (p:Pose)(k:Kv):Pose:=⟨p.m,p.a,p.b,offsetK k p.m +spotK k p.a+spotK k p.b+(axisK k).act p.x⟩
def torque (p:Pose)(k:Kv):ℝ:=omegaK k p.a*omegaK k p.b*trailK k p.m
variable [Module ℝ V]
lemma torn (X:Axis→Site n→V)(k:Kv)(p:Pose)(x:Site n):
 tip p (fun i b=> omegaK k i • X i (ferry k (b,i)).1) x = torque p k • tip (reed p k) X (decks k x):=by
     let B(i):= spotK k i; let s:=omegaK k; let L:=s p.a*s p.b; let G:= fwd p.a (X p.b)-fwd p.b (X p.a); let d:=B p.a+B p.b
     have ht(i j:Axis)(x): fwd i (fun b:Site n=> s j • X j (ferry k (b,j)).1) x=(s i*s j) • fwd i (X j) (decks k x +wrap _ (B i+B j)):=by
        unfold fwd B s; dsimp only; rw [ferry_at,ferry_at,deck_step]; try dsimp only
        unfold spotK omegaK; cases h:(axisK k).flip i <;> cases H:(axisK k).flip j <;> simp <;> abel_nf
     have he(l:List Axis)(x):Knot l (fun b=> L • G (decks k b+wrap n d)) x=(L*trailK k l) • Knot l G (decks k x +wrap n (offsetK k l + d)):=by
        induction l generalizing x with
        | nil=> simp [trailK,offsetK];rfl -- wrap
        | cons i l ih=>
          change Knot l _ (x+step i)-Knot l _ x=(L*(_*_)) • (Knot l G (_+step i)-Knot l G _)
          rw [ih,ih,deck_step]; dsimp only [offsetK]; unfold spotK omegaK; cases h:(axisK k).flip i <;> simp only [Bool.false_eq_true, ↓reduceIte,one_mul,zero_add,map_add,map_neg,wrap_step,neg_mul,mul_neg,neg_smul,smul_sub] <;> abel_nf
     unfold tip; rw [show (fwd p.a _-fwd p.b _)=(fun b=> L • G (decks k b+wrap n d)) from ?_,he]; swap
     · funext i; rw [Pi.sub_apply, ht, ht]; unfold L G d; rw [add_comm (B p.b),mul_comm (s p.b),Pi.sub_apply,smul_sub]
     congr 1; change Knot p.m G _= Knot p.m G _; congr 1; unfold reed d; simp only; unfold decks affine; rw [Signed.act_add]; simp only [wrap_signed, map_add, B]; abel
end YM.OPE.StageLight
