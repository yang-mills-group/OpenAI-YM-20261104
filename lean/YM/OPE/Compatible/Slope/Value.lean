import YM.OPE.Compatible.Slope.Bend
/-! Graded cost on moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset
open scoped Topology BigOperators Classical
variable {I J:Type*}[Fintype I][DecidableEq I]
def well (v: Shift I → ℝ)(f: Lieu I → ℝ):= ∑' x, v x*f (translit x)
def purewell (v: Shift I→ℝ)(d: ℕ): Prop:= ∀ l:List I,l.length<d→well v (tasting l)=0
-- estimates
variable {a:ℝ}{v:Shift I→ℝ}{d m n:ℕ}(h:Sack (poise m) v a)
omit [DecidableEq I] in
lemma taxes_well {f: Lieu I→ℝ} (hp:f∈Flavor I n) (g:n ≤ m)(h:Sack (poise m) v a):∃ C:ℝ,0 ≤ C ∧ SumBudget (fun x=> ‖v x*f (translit x)‖) (C*a):=by
    obtain ⟨b,hb,hh⟩:= tasting_cost (flavor_up g hp); refine ⟨b,hb,?_⟩; let u x:=poise m x*‖v x‖; let y i:=v i*f (translit i)
    have hs: SumBudget (fun x=> b*u x) (b*a):= ⟨fun i=>mul_nonneg hb (h.1 i), h.2.1.mul_left _,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hb⟩
    refine Work.F08.budget_minor hs (fun i=> norm_nonneg _) (fun i=>?_); rw [norm_mul,mul_comm ‖v i‖]; unfold u; rw [← mul_assoc b]; exact mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)
omit [DecidableEq I] in
lemma gardens {f: Lieu I→ℝ} (hp:f∈Flavor I m)(h:Sack (poise m) v a) :Summable fun x=>v x*f (translit x):= (taxes_well hp le_rfl h).choose_spec.2.2.1.of_norm
omit [DecidableEq I] in
lemma wells (P:purewell v d){f:Lieu I→ℝ}(H:f∈Flavor I n)(hg:n < d)(hm:n≤m)(hz:Sack (poise m) v a): well v f=0:=by
   apply flavor_elim H (fun f=> well v f=0) ?_ ?_ ?_ ?_
   · intro l hl;exact P _ (hl.trans_lt hg)
   · simp [well]
   · intro p q hp hq hx hy
     unfold well; simp only [Pi.add_apply,mul_add]; rw [Summable.tsum_add (gardens (flavor_up hm hp) hz) (gardens (flavor_up hm hq) hz)]; change well v p+well v q=_; rw [hx,hy,zero_add] -- `rw` ambiguous
   intro r p hp hx; unfold well; simp only [Pi.smul_apply,smul_eq_mul]; simp_rw [show ∀ x:Shift I,v x * (r * p (translit x))=r*(v x*p (translit x)) from fun x=>by ring,tsum_mul_left]; change r*well v p=0; rw [hx,mul_zero]
-- extend pine
omit [Fintype I] [DecidableEq I] in
private lemma pedal_curve (i:I)(n:ℕ) : ∃ f, f∈ Flavor I n ∧ ∀ x:Shift I, pedal (x i) n=f (translit x):=by
   induction n with
   | zero=>exact ⟨1,flavor_one 0,fun _=>rfl⟩
   | succ n ih=>
       obtain ⟨f,H,hf⟩:=ih; let g (x:Lieu I):= x i-(n:ℝ); let t:=f*g
       have hg:g∈ Flavor I 1:= (Flavor I 1).sub_mem (flavor_position i) (flavor_cast n 1)
       refine ⟨((n+1:ℝ)⁻¹:ℝ) • t,(Flavor I (n+1)).smul_mem _ (flavor_prod H hg),fun x=>?_⟩
       rw [pedal, hf x]; change f (translit x) *_/_=(n+1:ℝ)⁻¹*(f (translit x)*(x i-(n:ℝ))); ring
lemma pine_curve (i:Multiset I): ∃ f,f∈ Flavor I i.card ∧ ∀ x:Shift I, pine i x=f (translit x):=by
    choose p H h using fun j=> pedal_curve j (i.count j)
    have ht(s:Finset I): ((∏ j∈s,p j):Lieu I→ℝ)∈ Flavor I (∑ j∈s,i.count j):=by
       induction s using Finset.induction_on with
       | empty=>simp only [Finset.prod_empty,Finset.sum_empty]; exact flavor_one _
       | insert j s hj ih=>rw [Finset.sum_insert hj,Finset.prod_insert hj]; exact flavor_prod (H j) ih
    have hb : ∑ j, i.count j=i.card:=by
        induction i using Multiset.induction_on with
        | empty=>simp
        | @cons a i ih=> simp only [Multiset.count_cons,Multiset.card_cons]; simp [sum_add_distrib, *]
    exact ⟨∏ j,p j,hb ▸ ht _,fun x=>by unfold pine;simp [h]⟩
lemma newt (P:purewell v d) (hm:d ≤ m) (hz:Sack (poise m) v a): Abstemious d v:=fun i hi=>by obtain ⟨f,hg,H⟩:= pine_curve i; have he:= (trailed i d).mp hi; simp_rw [H]; exact wells P hg he (he.le.trans hm) hz
-- Uplift
variable {r:ℕ}
private lemma up_tasting (l:List (Keys (r+1))): ∃ f:Lieu (Keys r)→ℝ,f∈Flavor (Keys r) l.length ∧ ∀ x:Bin r,tasting l (translit (wreath r (0,x)))=f (translit x):=by
    let g (x:Lieu (Keys r)): Lieu (Keys (r+1)):= fun s=> Fin.cases 0 (fun i=>x (i,s.2)) s.1
    have hg (i:Keys (r+1)) :(fun x=> g x i) ∈ Flavor (Keys r) 1:=by
        obtain ⟨i,x⟩:=i; refine Fin.cases ?_ (fun j=> ?_) i
        · exact (Flavor _ _).zero_mem
        simpa [g] using flavor_position (j,x)
    refine ⟨(tasting l) ∘ g, flavor_diagonal _ hg (flavor_part _ _ le_rfl),fun x=>?_⟩
    refine congr_arg (tasting l) ?_
    ext ⟨i,s⟩; refine Fin.cases ?_ (fun j=>?_) i
    · change ((stepOut (wreath r (0,x)) 0 s:ℤ):ℝ)=0; rw [header]; simp
    change ((stepOut (wreath r (0,x)) j.succ s:ℤ):ℝ)=_; rw [flowPart,zero_add]; simp [g]; rfl
lemma uplight (p:Bin r→ℝ)(hp:purewell p d) (h:d≤m) (hv:Sack (poise m) p a): purewell (upland p) d:=by
   intro l hl
   unfold well; rw [← (wreath r).tsum_eq]; have hh: p ∈ (Set.univ:Set (Bin r→ℝ)):=Set.mem_univ _
   let f :Bin (r+1)→ℝ:= fun x=> upland p x*tasting l (translit x)
   have hs: Summable (f ∘ (wreath r)):= (wreath r).summable_iff.mpr (gardens (flavor_part _ _ (hl.le.trans h)) (upland_bill hv))
   change (∑' i:Cover × Bin r,(f ∘ (wreath r)) i)=_; rw [hs.tsum_prod]; -- notation
   obtain ⟨g,hg,hX⟩:= up_tasting l
   rw [tsum_eq_single (0:Cover)]
   · unfold f; simp only [comp_apply, upland,header,↓reduceIte,flattenZ,hX]; exact wells hp hg hl (hl.le.trans h) hv
   intro x hx; unfold f; simp [comp,upland,header,hx]
end YM.OPE.Flume
