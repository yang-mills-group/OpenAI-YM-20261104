import YM.MS.Wilson.Seed
/-!
# Discrete pure-basis jets in log link chart

Recursive forward-covariant-differences. Use actual group at every evaluation, so
 these are true gauge stencils at every closure (including alias). Minimal rank one
 from pure curvature.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Studio
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Draft Sew Chart Wilsonian
open Book Convolve Program Paint Logarithm
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P Q: Type}{F:Dot G P}
-- oriented plaques strictly <; sign outside
abbrev Rig (G:Gauge)(P:Type):= Edge P→ G.El
abbrev Eye (G:Gauge)(P:Type) := Rig G P →ℝ
def α (i:CI G) : G.Color→L[ℝ] ℝ:= ((baseC.toBasis).coord i).toContinuousLinearMap
lemma α_at (i:CI G)(q:G.Color): α i q=q i:= by simp [α,baseC]

def bolt₀ (U:Axis→G.El) := G.curvature (atCart U)
def bolt1 (j:CI G)(b:Lot G Axis):= α j (bolt₀ (G.lieExp ∘ b))
lemma curvatureArt (j:CI G): germ (bolt1 j):= by
   let U (b:Lot G Axis):= atCart (G.lieExp ∘ b)
   have he i : germ (fun b:Lot G Axis=> G.mat (G.lieExp (b i))):= G.exp_jet.contDiffAt.comp (f:=fun b:Lot G Axis=> b i) 0 (contDiff_apply ..|>.contDiffAt)
   let D : G.Mat≃L[ℝ] G.Mat:= starL ℝ
   have hR i : germ (fun b:Lot G Axis=>star (G.mat (G.lieExp (b i)))):= D.contDiff.contDiffAt.comp 0 (he i)
   have ht : germ (fun b=> G.mat (U b)):= by simp_rw [U,atCart,G.mat_mul,G.mat_inv]; exact (((he 0).mul (he 1)).mul (hR 2)).mul (hR 3)
   have hv : germ (fun b=>G.curvature (U b)):= by simp_rw [Gauge.curvature,G.mat_inv]; exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp 0 ((ht.sub (D.contDiff.contDiffAt.comp 0 ht)).const_smul (1/2:ℝ)) -- ext f composition type
   exact (α j).contDiff.contDiffAt.comp 0 hv
lemma gadj (i j:CI G): germ (fun b:G.Color=> weight (G.lieExp b) i j):= by
   let k (b:G.Color) :=G.mat (G.lieExp b); have he : germ k:= G.exp_jet.contDiffAt
   let D : G.Mat≃L[ℝ] G.Mat:= starL ℝ; let X:= baseC i;
   rw [show (fun b:G.Color => weight (G.lieExp b) i j)= α j ∘ fun b=> G.projectColor (k b * G.colorMat X * star (k b)) from funext fun b=> by rw [Function.comp_apply,α_at]; rfl]
   exact (α j).contDiff.contDiffAt.comp 0 (G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp 0 ((he.mul contDiffAt_const).mul (D.contDiff.contDiffAt.comp 0 he))) -- fix
lemma bolo_low (i:CI G): bolt1 i 0=0:= by simp [bolt1,bolt₀,atCart]
variable [AddCommGroup P][AddCommGroup Q] (d:Chart.Rail P) (L:PlaqAxes)
def tip (x:P)(U: Rig G P):= bolt₀ (U ∘ loadC d (x,L))
def tipSeed (x:P)(i:CI G) := art (loadC d (x,L)) (bolt1 i)
def bank (x:P)(a:Axis)(i j:CI G)(U:Rig G P):= weight (U (x,a)) i j
def bankSeed (x:P)(a:Axis)(i j:CI G) := onedge (x,a) (fun b:G.Color=> weight (G.lieExp b) i j)
-- cov jets. shift first curvature

def edgeSense (d:Chart.Rail P)(L:PlaqAxes): List Axis→ P→ Rig G P→ G.Color
   | [],x,U => tip d L x U
   | i::l,x,U =>G.adjoint (U (x,i)) (edgeSense d L l (x+d i) U) - edgeSense d L l x U

def clot (d:Chart.Rail P)(L:PlaqAxes): List Axis→ P→ CI G→ Dot G P
   | [],x,i=> tipSeed d L x i
   | a::l,x,i=> (∑ j: Conn G,couple DotFlip (clot d L l (x+d a) j) (bankSeed x a j i))-clot d L l x i
lemma clot_go (r:P→ Q)(g:Chart.Rail Q)(h:∀ i k,r (i+d k)=r i+g k)(l:List Axis)(x:P)(i: CI G): transport r (clot d L l x i)= clot g L l (r x) i:= by
   induction l generalizing x i with
   | nil=> rw [clot,clot,tipSeed,map_sec]; unfold tipSeed; congr 1; funext i; fin_cases i <;> simp [thread,loadC,h]
   | cons a l ih=> simp only [clot,map_sub,map_sum,transport_comes,bankSeed,onmove,ih,h]
lemma clot_tuned (l:List Axis)(x:P)(i:CI G): Tuned (clot d L l x i) 0:= by
   induction l generalizing x i with
   | nil=> exact Tune_port _ _ (curvatureArt _)
   | cons a l ih=> rw [clot]; exact (Tune.sum _ (fun j _=> (ih (x+d a) j).pair (Tune_edge _ _ (gadj ..)))).sub (ih ..)
lemma clot_zero (l:List Axis)(x:P)(i:CI G): (clot d L l x i).val []=0:= by
   induction l generalizing x i with
   | nil=> simp [clot,tipSeed,Sew.art,region,bolo_low]
   | cons a l ih=> simp only [clot,Submodule.coe_sub,Pi.sub_apply, sum_stack, Finset.sum_apply,coupled, nil_product,ih,zero_mul,Finset.sum_const_zero,sub_zero]
lemma clot_low (l:List Axis)(x:P)(i:CI G): From (clot d L l x i).val 1:= by
   rintro (_|r) hr; exact clot_zero ..; simp at hr; omega
-- evaluation at finite
lemma sight (l:List Axis)(x:P)(g:P→G.El)(U:Rig G P): edgeSense d L l x (siteGauge d g U)= G.adjoint (g x)⁻¹ (edgeSense d L l x U):= by
   induction l generalizing x with
   | nil=> rw [edgeSense,edgeSense,tip,bolt₀, class_cart]; simpa only [inv_inv,tip,bolt₀] using G.curvature_conjugate (g x)⁻¹ (atCart (U ∘ loadC d (x,L)))
   | cons a l ih=> rw [edgeSense,edgeSense,ih,ih,map_sub,siteGauge,endRail,← Gauge.adjoint_mul]; dsimp only; rw [mul_inv_cancel_right, G.adjoint_mul] -- check first ← group
lemma see (l:List Axis)(x:P)(c: G.ColorIndex)(g:P→ G.El)(U:Rig G P): α c (edgeSense d L l x (siteGauge d g U))=∑ i:CI G, weight (g x)⁻¹ i c * α i (edgeSense d L l x U):= by rw [sight]; simp_rw [α_at]; exact acts_all _ _ _
variable [DecidableEq P][Fintype P]
structure Reads (F:Dot G P)(f:Eye G P): Prop where
    born: germ (f ∘ nation)
    home: F.val= reads (f ∘ nation)
namespace Reads
variable {f g:Eye G P}{H:Dot G P}{I:Type*}
omit [AddCommGroup P] in
lemma pair (h:Reads F f)(v:Reads H g): Reads (couple DotFlip F H) (f*g):= ⟨h.born.mul v.born,by rw [coupled,h.home,v.home]; exact (ink_mul direction (glow G P |>.never) h.born v.born).symm⟩ -- need Glow.never qualification
omit [AddCommGroup P] in
lemma cash (c:ℝ)(h:Reads F f): Reads ((c:ℂ) • F) (c • f):=⟨h.born.const_smul c,by rw [smul_stack,h.home]; exact (ink_smul _ h.born _).symm⟩
omit [AddCommGroup P] in
lemma sum (J:Finset I){F:I→Dot G P}{f:I→Eye G P}(h:∀ i∈J,Reads (F i) (f i)): Reads (∑ i∈J,F i) (∑ i∈J,f i):= by
    have he : (∑ i∈J,f i) ∘ nation= ∑ i∈J,f i ∘ nation:= funext fun x=> by simp
    refine ⟨?_,?_⟩; rw [he,funext (fun x=> Finset.sum_apply x J (fun i=>f i ∘ nation))]; exact ContDiffAt.sum fun j hj=> (h j hj).born
    rw [sum_stack,he,reads,ink_sum _ _ (fun j hj=>(h j hj).born)]; exact Finset.sum_congr rfl (fun i hi=> (h i hi).home)
omit [AddCommGroup P] in
lemma sub (h:Reads F f)(v:Reads H g): Reads (F-H) (f-g):=⟨h.born.sub v.born,by rw [Submodule.coe_sub,h.home,v.home]; exact (ink_sub _ h.born v.born).symm⟩
end Reads
omit [AddCommGroup P] in
lemma bank_read (x:P)(a:Axis)(i j:CI G): Reads (bankSeed x a i j) (bank x a i j):=⟨(gadj i j).comp (f:=fun f: City G P=> f (x,a)) 0 (contDiffAt_apply ..),edge_parse _ (gadj ..)⟩ -- at apply
lemma clot_read (l:List Axis)(x:P)(i:CI G): Reads (clot d L l x i) (α i ∘ edgeSense d L l x):= by
   induction l generalizing x i with
   | nil=>
       let F:=pull (G:=G) (loadC d (x,L)); have ht := curvatureArt i; unfold germ at ht; rw [← show F (0:City G P)=0 from map_zero F] at ht -- actor
       exact ⟨ht.comp 0 F.contDiff.contDiffAt,pooled _ (curvatureArt i)⟩
   | cons a l ih=>
       have he : α i ∘ edgeSense d L (a::l) x= (∑ j:CI G,(α j ∘ edgeSense d L l (x+d a))* bank x a j i)-α i ∘ edgeSense d L l x:= by
           ext U; simp only [Function.comp_apply,edgeSense,map_sub,Pi.sub_apply,Finset.sum_apply,Pi.mul_apply,α_at]; congr 1; rw [acts_all]; apply Finset.sum_congr rfl; intro j _; exact mul_comm ..
       rw [clot,he]; exact (Reads.sum _ (fun j _=> Reads.pair (ih ..) (bank_read ..))).sub (ih ..)
end YM.MS.Native.Studio
