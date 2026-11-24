import YM.OPE.Compatible.Arch.Rock
import YM.PertExtension.Aspiration
/-!
# truncated formal near field. Reader oath
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
structure JetS (E:Type*) where
   s:E
   l:E
   h:E
namespace JetS
variable {k d:JetS E}
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma eta (k d:JetS E)(p:k.s=d.s)(q:k.l=d.l)(r:k.h=d.h): k=d:=by cases k; cases d; congr
instance : Add (JetS E):=⟨fun p q=>⟨p.s+q.s,p.l+q.l,p.h+q.h⟩⟩
instance : Neg (JetS E):=⟨fun p=>⟨-p.s,-p.l,-p.h⟩⟩
instance : Sub (JetS E):=⟨fun p q=> p+ -q⟩
instance : SMul ℝ (JetS E):=⟨fun s p=>⟨s • p.s,s • p.l,s • p.h⟩⟩
instance : Zero (JetS E):=⟨⟨0,0,0⟩⟩
instance : One (JetS ℝ) :=⟨⟨1,0,0⟩⟩
instance : Mul (JetS ℝ):=⟨fun k d=> ⟨k.s*d.s,k.s*d.l+k.l*d.s,k.s*d.h+k.l*d.l+k.h*d.s⟩⟩
def atK (k:JetS E)(t:ℝ):E:= k.s+t • k.l+(t^2) • k.h
def seq (k:JetS E): ℕ→E
|0=>k.s
|1=>k.l
|2=>k.h
|_=>0
lemma atK_seq (k:JetS E)(t:ℝ): Tested.peval k.seq 2 t=k.atK t:=by simp [Tested.peval,Zone.eval, atK,Finset.sum_range_succ,seq]
lemma rates_add (k d:JetS E): (k+d).atK=k.atK+d.atK:=by funext i; change k.s+_+_+_=_; unfold atK; simp only [Pi.add_apply, show (k+d).l=k.l+d.l from rfl,show (k+d).h=k.h+d.h from rfl,smul_add]; abel
@[simp] lemma rates_neg (k:JetS E): (-k).atK=-k.atK:=by funext i; change -k.s+i • (-_) + i^2 • (-_) = -(k.s+_+_); rw [smul_neg,smul_neg]; abel
@[simp] lemma rates_scale (k:JetS E)(c:ℝ):(c • k).atK=c • k.atK:=by funext i; change c • k.s + i • (c • k.l)+ i^2 • (c • k.h)=c • _; rw [atK,smul_add,smul_add,smul_comm i, smul_comm (i^2)]
end JetS
local notation "Lf" => Tested.germ
abbrev gradeP (n: ℕ) := fun x:ℝ=> x^n
def Reads (f:ℝ→E)(k:JetS E):Prop:= (f-k.atK)=O[Lf](gradeP 3)
namespace Reads
variable {f h : ℝ→ E}{k q:JetS E}
omit [NormedSpace ℝ E] in lemma isTariff {n:ℕ} : f=O[Lf](gradeP n) ↔ Tested.Bill n f:=by
   rw [isBigO_iff]; constructor
   · rintro ⟨a,ha⟩; unfold Tested.Bill; refine ⟨max a 0,(le_max_right ..),?_⟩; filter_upwards [ha,Tested.eventually_pos] with x hx he; rw [Real.norm_eq_abs (gradeP n x),abs_of_nonneg (show 0≤gradeP n x from pow_nonneg he.le _)] at hx; exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg he.le _))
   rintro ⟨a,_,ha⟩; refine ⟨a,?_⟩; filter_upwards [ha,Tested.eventually_pos] with x hx he; rw [Real.norm_eq_abs (gradeP n x),abs_of_nonneg (show 0≤gradeP n x from pow_nonneg he.le _)]; exact hx
lemma knee (n:ℕ)(k:JetS E)(h:n≤2): ((k.atK-Tested.peval k.seq n): ℝ→E)=O[Lf](gradeP (n+1)):=by
     have he:= (Tested.Aspiration.polynomial k.seq 2) n; apply isTariff.mpr; convert he using 1
     ext1 i; rw [Pi.sub_apply, Pi.sub_apply,k.atK_seq]; congr 1; unfold Tested.peval Zone.eval; exact Finset.sum_congr rfl fun j hj=>by dsimp only; rw [if_pos (by simp only [Finset.mem_range] at hj;omega: j ≤ 2)]
lemma origin (hq:Reads f k)(n:ℕ)(h:n ≤ 2): Tested.Bill (n+1) ((f-Tested.peval k.seq n): ℝ→E):=by
    rw [show f-_=(f-k.atK)+(k.atK-Tested.peval k.seq n) by abel]; exact Tested.bill_add (Tested.bill_ge (isTariff.mp hq) (by omega)) (isTariff.mp (knee _ _ h))
-- finite uniqueness
lemma equality (p:Reads f k)(h:Reads f q): k=q:=by
   have he(i:ℕ)(hx:i≤2): k.seq i=q.seq i:=by
    induction i using Nat.strong_induction_on with
    | _ i ih =>
     have hh(j:ℕ)(hv:j < i): k.seq j=q.seq j:=ih j hv (hv.le.trans hx)
     obtain ⟨a,ha,hA⟩:= origin p i hx; obtain ⟨b,hb,hB⟩:=origin h i hx
     by_contra H; let z:= ‖k.seq i-q.seq i‖; have hz:0<z:= norm_pos_iff.mpr (sub_ne_zero.mpr H)
     obtain ⟨t,hf,hg,ht,hk⟩:= (hA.and (hB.and (Tested.eventually_small (show 0< z/(a+b+1) by positivity)))).exists
     have HL: t^i*z ≤ (a+b)*t*t^i:=by
          have he : Tested.peval k.seq i t-Tested.peval q.seq i t=t^i • (k.seq i-q.seq i):=by unfold Tested.peval Zone.eval; rw [Finset.sum_range_succ,Finset.sum_range_succ, show ∑ j∈Finset.range i,(t^j) • k.seq j=∑ j∈Finset.range i,(t^j) • q.seq j from Finset.sum_congr rfl (fun j hj=> by rw [hh j (Finset.mem_range.mp hj)])]; rw [smul_sub]; abel
          rw [show t^i*z=‖(t^i) • (k.seq i-q.seq i)‖ by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos ht _)], ← he, show Tested.peval k.seq i t-Tested.peval q.seq i t=((f-Tested.peval q.seq i) t)-((f-Tested.peval k.seq i) t) by simp only [Pi.sub_apply]; abel]; exact (norm_sub_le ..).trans ((add_le_add hg hf).trans_eq (by rw [pow_succ]; ring))
     rw [mul_comm (t^i),mul_le_mul_iff_of_pos_right (pow_pos ht _)] at HL; have hv:= (lt_div_iff₀ (show 0<a+b+1 by positivity)).mp hk; linarith
   exact JetS.eta _ _ (he 0 (by decide)) (he 1 (by decide)) (he 2 le_rfl)
end Reads
end YM.OPE.Libra
