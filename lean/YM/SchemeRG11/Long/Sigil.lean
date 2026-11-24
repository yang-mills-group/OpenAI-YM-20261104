import YM.SchemeRG11.Long.Ash
/-! Engineering/Taylor valuation CLASS. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial Outlook
open scoped Classical Pointwise
variable {G:Gauge} {T:Align.Itinerary} {n:ℕ} {f g:Ban G} {u v:ℤ}
abbrev Size(G:Gauge)(n:ℕ):= Sky G n→₀ℕ
def scriptum(n:ℕ)(f:Ban G)(a:Size G n):Slate:=fun m p=> MvPolynomial.coeff a (inlay G n (f m p))
abbrev bill {n:ℕ}(v:Size G n):ℤ:=rankW inkAge v
structure Sigil(T:Align.Itinerary)(n:ℕ)(u:ℤ)(f:Ban G): Prop where
 key (a:Size G n): Plain T (bill a-u) (scriptum n f a)
 safe:∃ F:Finset (Size G n),∀ i x,(inlay G n (f i x)).support ⊆ F
namespace Sigil
lemma zero : Sigil T n u (0:Ban G):= ⟨fun a=> by convert Plain.zero using 1; funext k x; simp [scriptum],⟨∅, by simp⟩⟩
lemma unit:Sigil T n 0 (castV (G:=G) 1):=by
 refine ⟨fun a=>?_, ⟨(inlay G n 1).support,fun _ _=>Finset.Subset.refl _⟩⟩; unfold scriptum; simp only [castV,map_one, coeff_one]; by_cases h:a=0
 · subst a; rw [show bill (0:Size G n)=0 by simp [bill,rankW], sub_self]; simp only [if_true]; apply Plain.const
 have hr:(if (0:Size G n)=a then (1:ℝ) else 0)=0:=if_neg (Ne.symm h); simp_rw [hr]; exact Plain.zero
lemma add(h:Sigil T n u f)(k:Sigil T n u g):Sigil T n u (f+g):=by
 refine ⟨fun a=> ?_,⟨h.2.choose ∪ k.2.choose, fun i x=>?_⟩⟩
 · convert (h.1 a).add (k.1 a) using 1; funext i x; simp only [scriptum,Pi.add_apply,map_add,coeff_add]
 simp only [Pi.add_apply,map_add]; exact Finset.Subset.trans MvPolynomial.support_add (Finset.union_subset_union (h.2.choose_spec i x) (k.2.choose_spec i x))
lemma mul (h:Sigil T n u f)(k:Sigil T n v g): Sigil T n (u+v) (f*g):=by
 let F:= h.2.choose; let G':=k.2.choose
 refine ⟨fun a=>?_,⟨F+G',fun i p=>?_⟩⟩
 · unfold scriptum; simp_rw [Pi.mul_apply,map_mul, coeff_mul]; apply Plain.piles _ (f:=fun (q: Size G n × Size G n)=>scriptum n f q.1 * scriptum n g q.2)
   intro x w; have hx:x.1+x.2=a:= Finset.HasAntidiagonal.mem_antidiagonal.mp w
   rw [show bill a-(u+v)= (bill x.1-u)+(bill x.2-v) by unfold bill rankW; rw [← hx,map_add]; omega]; exact (h.1 x.1).mul (k.1 x.2)
 simp only [Pi.mul_apply,map_mul]; intro b hb; obtain ⟨i,h',j,H,x⟩:=Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb); exact Finset.mem_add.mpr ⟨i,h.2.choose_spec _ _ h',j,k.2.choose_spec _ _ H,x⟩
lemma scal (h:Sigil T n u f){e:Slate}(k:Plain T (-v) e): Sigil T n (v+u) (play e f):=by
 refine ⟨fun a=>?_,⟨h.2.choose,fun i x=>?_⟩⟩
 · rw [show bill a-(v+u)= -v + (bill a-u) by omega]; convert k.mul (h.1 a) using 1; funext i x; simp only [scriptum,play,map_smul,coeff_smul]; rfl
 simp only [play,map_smul]; refine Finset.Subset.trans ?_ (h.2.choose_spec i x); intro y hy; have ht:=mem_support_iff.mp hy; rw [coeff_smul] at ht; exact mem_support_iff.mpr fun w=> ht (by rw [w,smul_zero])
lemma cabin(h:Sigil T n u f)(r:ℝ): Sigil T n u (fun i p=>r • f i p):=by
 have he:=h.scal (v:=0) (show Plain T (-0) _ from (show -(0:ℤ)=0 from neg_zero) ▸ Plain.const r); rw [zero_add] at he; exact he
lemma regalia(n:ℕ)(p:Touch G):inlay G n (leaf p)= ∑ i:Sky G n, sense (cant (plum i)) p • X i:=by
 apply MvPolynomial.funext; intro x; simp_rw [←aeval_eq_eval,rise_cast,Haze.realTaste,lump ]
 -- pass
 rw [_root_.map_sum]; simp only [map_smul,aeval_X]; induction p using Finsupp.induction_linear with
 | zero=> simp only [map_zero,zero_smul,Finset.sum_const_zero]
 | add a b ha hb=> simp only [map_add,add_smul, Finset.sum_add_distrib,ha,hb]
 | single p a=>
    simp only [cant,sense,Finsupp.linearCombination_single,WithLp.ofLp_sum, PiLp.smul_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=>by ring
lemma singly {m:ℕ}(p:Touch G)(hp:p∈ Stepper G m) (θ:Bool):Sigil T n (m+1:ℤ) (if θ then castV (leaf p) else swift p):=by
 let f:= (if θ then castV (leaf p) else swift p)
 let t:Cover→ Cover:=fun x=> if θ then 0 else x
 let L:= fun (a:Sky G n) z=>sense (cant (plum a)) (flex (t z) p)
 have hj(i:ℕ)(z:Cover): inlay G n (f i z)=∑ a:Sky G n,L a z • X a:=by
   unfold f L t; cases θ <;> simp only [↓reduceIte,Bool.false_eq_true, swift,castV,regalia,flex_zero] -- t before L maybe
 refine ⟨fun a=>?_, ⟨Finset.univ.image (fun i:Sky G n=>Finsupp.single i (1:ℕ)),fun i x j e=>?_⟩⟩
 · have H(a:Size G n):scriptum n f a=fun i p=>∑z:Sky G n,(L z p :ℝ) * coeff a (X z:Sketch G n):=by unfold scriptum; funext i p; simp only [hj,coeff_sum,coeff_smul,smul_eq_mul]
   rw [H a]; apply Plain.piles _ _ -- test
   intro i _; by_cases he:Finsupp.single i (1:ℕ)=a
   · rw [←he,show bill (Finsupp.single i 1)=(inkAge i:ℤ) from by unfold bill rankW; simp only [Finsupp.weight_single,one_smul]]
     simp only [coeff_X,if_true,mul_one]; by_cases hc:θ = true
     · subst θ; unfold L t; simp only [if_true,flex_zero]
       by_cases hh: (inkAge i:ℤ)< m+1
       · rw [plum,← flex_zero p,sail (clouded i) (by omega) p hp]; exact Plain.zero
       exact (Plain.const _).widened (by omega)
     unfold L t; simp_rw [if_neg hc]; exact stamp p hp i
   simp only [coeff_X,if_neg he,mul_zero];exact Plain.zero
 have hw:=mem_support_iff.mp e; rw [hj,coeff_sum] at hw; by_contra h
 apply hw; apply Finset.sum_eq_zero; intro y hy; rw [coeff_smul,coeff_X,if_neg (fun w=>h (Finset.mem_image.mpr ⟨y,hy,w⟩)),smul_zero]
end Sigil

def crystalline (T: Align.Itinerary)(G:Gauge)(m:ℕ): Volume G T where
 classV := Sigil T m
 nest x b h := by induction h with
   | unit=> exact Sigil.unit
   | zero=> exact Sigil.zero
   | piece p v=>exact Sigil.singly p v false
   | add h k a b=>exact a.add b
   | mul h k a b=>exact a.mul b
   | scale h a b=> exact b.scal a
 add := Sigil.add
 coin :=fun _ _ c h=> h.cabin c
 mul := Sigil.mul
 scale:= fun h p=> h.scal p
 anchor a k h:= Sigil.singly a h true
end YM.SchemeRG11.Long
