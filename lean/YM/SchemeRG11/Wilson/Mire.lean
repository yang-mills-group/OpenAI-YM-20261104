import YM.SchemeRG11.Wilson.Cold
import YM.Work.E01
/-! Far torus including inversion image charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G: Gauge} {I J:Type*} {N:Side}
lemma wrapcost {k:ℕ} (x:Cover)(h:diam x≤ k): x∈box k:=by
 have he i: (x i).natAbs ≤ k:=(diam_ge _ _).trans h
 rw [box_test]; constructor <;> (intro i; specialize he i; omega)
lemma wrapcost₂ {k:ℕ}(x:Cover)(h:x∈box k):diam x≤ k:=by
 unfold diam; apply Finset.sup_le; intro i _; have hi:=(box_test.mp h).1 i; have hh:=(box_test.mp h).2 i; omega
lemma mod_le (v:Cover) : pdist (wrap N v) ≤ diam v:= Work.E01.pdist_wrap_le (wrapcost v le_rfl)
lemma stepP (i: Axis): pdist (step i:Site N)≤1:=by rw [←wrap_step]; apply Work.E01.pdist_wrap_le (box_test.mpr ⟨?_,?_⟩) <;> (intro j; rw [step_apply]; split <;> norm_num)

def velvet (i:Site N)(t:I→Site N): noteB G I→ Pill G N :=Sum.elim (veil i) (fun b=> veil (t b.1) b.2)
open Dose
lemma tailO (s:Finset I)(p:I→vellum G)(i j:Axis): ∃ W>0,∀ {N:Side}(x:Site N)(t:I→Site N)(n:ℝ),0≤n→(∀ b:I, n≤(pdist (t b-x)+1:ℝ))→(∀ b:I, n ≤ (pdist (t b+x)+1:ℝ))→
 |(spray G N).avg (Tree.cost x i j * ∏ u∈s,adsorb (t u) (p u))| * n^6 ≤ W:=by
 obtain ⟨C,hC,H⟩:=Catch.far []
 obtain ⟨K,hK,M⟩:=remotePrice (fun (_ _ : noteB G I)=> (2*C:ℝ)) Sum.inl Sum.inr (gradeFace (0:Cover) i j (G:=G)) (summit (2*C)) (glen s p)
 refine ⟨K,hK,?_⟩; intro N x t n hn hg hr
 have he(z:Site N): |thread z| * (pdist z+1:ℝ)^2 ≤ C:= H z
 have hh(z:Site N): |thread z| ≤ C:= (le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (show 1 ≤ pdist z+(1:ℝ) from by simp))).trans (he z)
 let V:=spray G N; let f:=velvet (G:=G) x t
 have h1:Tops (V.pull (Dose.arrow f)) (fun _ _=>2*C):=by
   intro a b; rw [Dose.reach,spray_eq]; split
   · apply (abs_sub ..).trans; apply (add_le_add (hh _) (hh _)).trans; ring_nf; apply le_rfl
   rw [abs_zero];positivity
 have h2(a:Shaft G)(b:I× Shaft G): |V.pulse (f (.inl a)) (f (.inr b))| * n^2 ≤ summit (2*C) (Sum.inl a) (Sum.inr b):=by
   let u:=a.1.1; let v:=b.2.1.1;let y:=t b.1
   let A := wrap N u+x; let B:=wrap N v+y; let D : ℝ:=1+(diam u:ℝ)+(diam v:ℝ)+2
   have hd : 0<D:=by unfold D; positivity
   have he' : summit (2*C) (Sum.inl a) (Sum.inr b)=2*C*D^2:=rfl
   rw [he',spray_eq]; split; swap; · rw [abs_zero,zero_mul]; positivity
   change |thread (B-A)-thread (B+A+step a.1.2)| * n^2≤_
   have hm : pdist (y-x) ≤ pdist (B-A)+diam u+diam v+1 :=by calc
      _ = pdist (B-A+wrap _ u+ -wrap _ v) := by unfold A B; congr 1; abel
      _ ≤ pdist (B-A+wrap _ u)+pdist (-wrap _ v) := pdist_triangle _ _
      _ ≤ _ := by rw [pdist_neg]; have := mod_le (N:=N) v; have := mod_le (N:=N) u; have := pdist_triangle (B-A) (wrap _ u); omega
   let L := step (S:=Per N) a.1.2
   have hv : pdist (y+x) ≤ pdist (B+A+L)+diam u+diam v+1:=by
     let E:=B+A+L; have hs: pdist (-L) ≤1:=by rw [pdist_neg]; apply stepP
     calc
      _ = pdist (E+ -(wrap _ u) + -(wrap _ v)+ -L) := by unfold E A B; congr 1; abel
      _ ≤ pdist (E+ -wrap _ u+ -wrap _ v)+pdist (-L):= pdist_triangle ..
      _ ≤ _ := by
        apply le_trans (Nat.add_le_add (pdist_triangle (E+ -wrap _ u) (-wrap _ v)) hs); gcongr; apply (pdist_triangle E (-wrap _ u)).trans; rw [pdist_neg]; gcongr; apply mod_le
        rw [pdist_neg]; apply mod_le
   have ht(z w:Site N)(hb:n≤(pdist w+1:ℝ))(hw:pdist w≤pdist z +diam u+diam v+1):|thread z| * n^2≤ C*D^2:=by
     have he' : (pdist w:ℝ) ≤ pdist z+(diam u:ℝ)+(diam v:ℝ)+1:=by exact_mod_cast hw
     have he'':n ≤ (pdist z+1:ℝ)*D:=by dsimp [D]; nlinarith only [he',hb,show (pdist z:ℝ) ≥ 0 from by positivity, show (0:ℝ) ≤ diam u from by positivity,show (0:ℝ) ≤ diam v from by positivity, show (0:ℝ)≤(pdist z:ℝ)*(diam u+diam v:ℝ) from by positivity]
     apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn he'' 2) (abs_nonneg _)).trans; rw [mul_pow,←mul_assoc]; gcongr; exact he z
   apply (mul_le_mul_of_nonneg_right (abs_sub ..) (sq_nonneg _)).trans; rw [add_mul]
   nlinarith only [ht (B-A) (y-x) (hg b.1) hm, ht (B+A+step a.1.2) (y+x) (hr b.1) hv]
 specialize M (V.pull (Dose.arrow f)) (n^2) h1 (sq_nonneg _) (fun i j=>by rw [reach]; apply h2)
 have h3(a b:Shaft G)(he:a.2≠b.2): V.pulse (f (.inl a)) (f (.inl b))=0:=by rw [spray_eq, if_neg]; intro h; exact he h.1
 rw [← mileageC p s f V 0 i j (fun u=>veil (t u.1) u.2) (fun _=>rfl) h3, ← pow_mul, show rename (fun a=> f (.inl a)) (Tree.cost 0 i j)=Tree.cost x i j from by change adsorb x _= _; rw [induced,map_zero,zero_add]] at M
 exact M
end YM.SchemeRG11.Acorn
