import YM.SchemeRG11.Plate.Omen
/-! Every order-one bare face far from all marks has three propagators gain. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G: Gauge} {I J:Type*} {N:Side}
abbrev noteB(G: Gauge)(I:Type*):= Shaft G ⊕ (I × Shaft G)
variable (p:I→ vellum G)(s:Finset I)
open Dose
lemma mileageC (a:noteB G I→J)(D:Dose J ℝ)(x:Cover)(i j:Axis) (w:I× Shaft G→J)
   (ha:∀ (p:I× Shaft G), a (.inr p)=w p)(hd: ∀ (p q:Shaft G), p.2≠q.2→D.pulse (a (.inl p)) (a (.inl q))=0):
 D.avg (rename (fun d:Shaft G=> a (.inl d)) (Tree.cost x i j)*(∏ i∈s,rename (fun c:Shaft G=> w (i,c)) (p i)))=
   (D.pull (Dose.arrow a)).avg ((D.pull (Dose.arrow a)).neg.heat (rename Sum.inl (Tree.cost x i j))*rename Sum.inr (glen s p)) :=by
 let M(I:noteB G _):Stem J ℝ:=arrow a I
 let L:=D.pull (Dose.arrow a); have he: L.heat (rename Sum.inl (Tree.cost x i j))=rename Sum.inl (Tree.cost x i j):=by
   rw [L.migrate, vapid x i j]
   intro a' b h; rw [Dose.reach]; unfold L; rw [Dose.reach]; exact hd a' b h
 rw [show L.neg.heat (rename Sum.inl (Tree.cost x i j))=rename Sum.inl (Tree.cost x i j) from (congrArg L.neg.heat he.symm).trans (L.opposite _),← D.colour]
 rw [← Dose.rebase,map_mul (rename a),rename_rename,rename_rename]
 congr 2
 simp_rw [← ha]; exact (spell (fun k d=> a (.inr (k,d))) s p).symm
abbrev costCover (a : Shaft G)(b:Shaft G) :ℝ:= (1+(diam a.1.1:ℝ)+(diam b.1.1:ℝ) +2)^2
lemma growDistance (x y u v:Cover):
 (diam (x-y)+1:ℝ) ≤ (1+(diam u:ℝ)+(diam v:ℝ)+2)*(diam ((u+x)-(v+y))+1:ℝ):=by
 let n:=diam ((u+x)-(v+y)); let m:=diam u; let l:=diam v
 have h:diam (x-y)≤n+m+l:=by
   have h1:=diam_add ((u+x)-(v+y)) (-u); rw [diam_neg] at h1
   calc _ = diam (((u+x)-(v+y))+(-u)+v):=by congr 1; abel
        _ ≤ _:= (diam_add _ _).trans (Nat.add_le_add_right h1 l)
 have ht : (diam (x-y):ℝ)≤ n+(m:ℝ)+(l:ℝ):=by exact_mod_cast h
 change _≤ (1+(m:ℝ)+(l:ℝ)+2)*(n+1:ℝ)
 nlinarith [show (0:ℝ) ≤ n from by positivity,show (0:ℝ) ≤ m from by positivity,show (0:ℝ) ≤ l from by positivity]

def red(z:Cover)(t:I → Cover): noteB G I→ Shaft G| .inl p => rise z p| .inr (u,p)=>rise (t u) p
def summit (C:ℝ): noteB G I→ noteB G I→ℝ|.inl p,.inr (_,q)=>C*costCover p q|_,_=>C
lemma tailC (i j: Axis): ∃ W>0, ∀ (x:Cover) (t:I → Cover) (n:ℝ),0≤n→(∀ i:I, n≤(diam (x-t i)+1:ℝ))→
 |(land G).avg (Tree.cost x i j*aerial s p t)| * n^6 ≤ W:=by
 obtain ⟨C,hC,H⟩:=Catch.payment []
 obtain ⟨K,hK,M⟩:=remotePrice (fun (_ _ : noteB G I)=>C) Sum.inl Sum.inr (gradeFace (0:Cover) i j (G:=G)) (summit C) (glen s p)
 have he z: |coverLine z| * (diam z+1:ℝ)^2 ≤ C:=H z
 have hh z: |coverLine z| ≤ C:=(le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (show 1≤(diam z+1:ℝ) by linarith [show 0≤(diam z:ℝ) from by positivity]))).trans (he z)
 refine ⟨K,hK,?_⟩; intro x t n hn ho
 let f:=red (G:=G) x t; let L:=land G
 have h1: Tops (L.pull (Dose.arrow f)) (fun _ _=> C):=by
   intro a b; rw [reach]; unfold L land; dsimp only; split; · apply hh
   simpa using hC.le
 have h2(a:Shaft G)(b:I×Shaft G): |L.pulse (f (.inl a)) (f (.inr b))| * n^2 ≤ summit C (Sum.inl a) (Sum.inr b):=by
   let q:= b.2; unfold summit; dsimp only; unfold L land; dsimp only; split <;> rename_i hr
   · let k:=q.1.1; let u:=a.1.1
     let W:=(u+x)-(k+t b.1)
     change |coverLine W| * n^2 ≤ C*costCover a q
     let E:=(diam W+1:ℝ)
     have hx:=he W
     have hv:n ≤ (1+(diam u:ℝ)+(diam k:ℝ)+2)*E:= (ho b.1).trans (growDistance x (t b.1) u k)
     calc _ ≤ |coverLine W| * ((1+(diam u:ℝ)+(diam k:ℝ)+2)*E)^2:=by gcongr
          _ = (|coverLine W| * E^2)*costCover a q:=by unfold costCover u k; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
   rw [abs_zero,zero_mul]; exact mul_nonneg hC.le (sq_nonneg _)
 have h3(a b:Shaft G)(hr:a.2≠b.2): L.pulse (f (.inl a)) (f (.inl b))=0:=if_neg (fun v=>hr v.1)
 let S:= L.avg (Tree.cost x i j*aerial s p t)
 specialize M (L.pull (Dose.arrow f)) (n^2) h1 (sq_nonneg _) (fun i j=>by rw [reach]; apply h2)
 rw [← mileageC p s f L (0:Cover) i j (fun d=> f (.inr d)) (fun _=> rfl) h3, show rename (fun u:Shaft G=> f (.inl u)) (Tree.cost 0 i j)=Tree.cost x i j from honour .., ← pow_mul] at M; exact M
end YM.SchemeRG11.Acorn
