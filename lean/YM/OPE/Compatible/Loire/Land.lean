import YM.OPE.Compatible.Loire.Desk
/-!
# Finite body loans (arbitrary links, not-for-chart fitting).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script Flock StageLight Balsam Nestle
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {U:Gloam}{G:Gauge}{i:ℕ}{K:KernelChoices}
variable (H:∀ j,Even (U.M j).val)
abbrev IpT (G:Gauge):= (p:ℕ)→ Keys G (Limb (H p))→ℝ
local notation "X!"=> IpT H G
local notation "W!"=> fun i=> Chart.tangent G (Limb (H i))
def shucks (l:List (Yarn U G))(p:ℕ)(v:Keys G (Limb (H p))):ℝ:=∏ i:Fin l.length, slips H (l.get i) p v
lemma slices (l p:List (Yarn U G)): shucks H (l++p)=shucks H l*shucks H p:=by
    induction l with
    | nil=> ext x i; simp [shucks];rfl
    | cons a l ih=>
      funext i v; simp only[Pi.mul_apply]; rw [List.cons_append, show shucks H (a::(l++p)) i v=_ from leafcons a .., show shucks H (a::l) i v=_ from leafcons a l i v, ih, Pi.mul_apply, Pi.mul_apply];ring
where leafcons (a:Yarn U G)(l:List (Yarn U G))(p:ℕ)(v:Keys G (Limb (H p))): shucks H (a::l) p v= slips H a p v*shucks H l p v:= Fin.prod_univ_succ ..
inductive Tar : X!→ Prop
| monom (i:List (Yarn U G)) : Tar (shucks H i)
| add {x y} : Tar x → Tar y → Tar (x+y)
| scale {x} (c:ℝ): Tar x → Tar (c•x)
lemma Tar_bond {x:X!}(h:Tar H x)(j:ℕ):Bond (x j):=by
   induction h with
   | monom a=>unfold shucks; exact Bond.product _ Finset.univ (fun i _=> Bond.glyph _)
   | add _ _ ht hp=> exact ht.add hp
   | scale a _ ht=> exact ht.scale _
lemma Tar_mul {x y:X!}(hx:Tar H x)(hy:Tar H y):Tar H (x*y):=by
    induction hx with
    | add _ _ hp hx=> rw [add_mul]; exact Tar.add hp hx
    | scale c _ hp=> rw [smul_mul_assoc]; exact Tar.scale c hp
    | monom l=> induction hy with
         | add _ _ h k=> rw [mul_add]; exact Tar.add h k
         | scale i _ h=> rw [mul_smul_comm]; exact Tar.scale i h
         | monom p=> rw [← slices]; exact Tar.monom _
lemma seeds (p:List (Yarn U G))(i:ℕ): shucks H p i= fauna (fun _ _=> (0:ℝ)) (fun j=> slips H (p.get j) i) Finset.univ:=by
    let L:=fun j=> slips H (p.get j) i; have he(t:Finset (Fin p.length)):fauna (fun _ _=>0) L t= ∏ i∈t,(⇑(L i)):=by
        induction t using Finset.strongInduction with | _ s ih
        obtain rfl|h:= s.eq_empty_or_nonempty
        · simp only [fanE,Finset.prod_empty]
        rw [pier _ _ (innerA h), ih _ (Finset.erase_ssubset (innerA h).1)]; simp only [zero_smul,Finset.sum_const_zero,sub_zero]; exact Finset.mul_prod_erase s (fun i=> ⇑(L i)) (innerA h).1
    erw [he]; funext x; rw [Finset.prod_apply];rfl
lemma taxes (hp:4≤ i){f:X!}(ht:Tar H f) : Cleared U (fun j=> (boost (H j) (Train.top i) hp K).average ((W!) j) (f j)):=by
    induction ht with
    | monom l=>
      let g:= fun n:ℕ=> boost (H n) (Train.top i) hp K (G:=G)
      obtain ⟨C,H'⟩:=grime (μ:=W!) (L:=g) (d:=fun _=>0) (K:=fun _ _=>0) (U:=U) (A:=fun i a=>slips H (l.get a) i) Finset.univ (by intro a _ b _ h; change Cleared U (fun i=>(U.h i^0)⁻¹*((g i).wick (slips H _ i) (slips H _ i)-0)); simp only [pow_zero,inv_one,one_mul,sub_zero]; exact bis (C:=K) H hp (l.get a) (l.get b))
      simp_rw [seeds]; exact H'.full
    | @add x y h hp' he hv=> convert! he.fuse hv using 2 with i; exact sun _ _ (Tar_bond H h i) (Tar_bond H hp' i)
    | @scale x c h ih=>convert! (ih.glu (c • ContinuousLinearMap.id ℝ ℝ)) using 2 with i; exact scooted ..
end YM.OPE.Shrew
