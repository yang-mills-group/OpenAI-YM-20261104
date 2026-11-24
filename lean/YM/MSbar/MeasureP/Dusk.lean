import YM.MSbar.Whisk.Span
import YM.Corona.Spend
import YM.Next.FREE_KERNELS.Traffic
/-! Native scale length loss for weighted rooted lyrics. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Set Function Filter Lattice Whisk
open scoped Topology BigOperators
variable {α β γ:Type}
-- When head/tail without proofs.Volunteer
noncomputable def beads (f:α→β→ℝ): List α → List β→ℝ
| [],_=>1
| _::_,[]=>1
| i::l,w::h=> f i w*beads f l h
noncomputable def tube(f:α→β→ℕ): List α→List β →ℕ
| [],_=>0| _::_,[]=>0|i::l,w::h=>f i w+tube f l h
lemma kids (f:α→β→ℝ)(h:∀ i j,0≤f i j)(x:List α)(y:List β):0≤beads f x y:=by induction x generalizing y with |nil=>simp [beads]|cons a x ih=> cases y; simp [beads]; exact mul_nonneg (h ..) (ih _)
section
variable {c n:Side}(g : Ratio c n) (f:α→Site n)(v:β→Site c)
open Next.Free
local notation "Q" =>g.count.val
local notation "B"=>(g.count.val:ℝ)
local notation "p📫"=> fun (x:α)(w:β)=>separation (f x) (g.embed (v w))
open scoped Classical
variable [Fintype α][Fintype β]
lemma tang (l:List α)(h:List β)(hh:h.length=l.length)(j:Site c)(hj:j∈Whisk.zone v ∅ h):∃ i ∈ Whisk.zone f ∅ l, separation i (g.embed j) ≤ tube (fun x w=> separation (f x) (g.embed (v w))) l h :=by
   induction l generalizing h with
   | nil=> simp [show h=[] by simpa using hh,Whisk.zone] at hj
   | cons a l ih=> cases h with
                   | nil=> simp at hh
                   | cons y h=> rw [added,Finset.mem_insert] at hj; rcases hj with hj|hj
                                · rw [added,hj]; exact ⟨f a,Finset.mem_insert_self _ _,by simp [tube]⟩
                                obtain ⟨i,hi,hv⟩:= ih h (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hh) hj
                                rw [added]; exact ⟨i,Finset.mem_insert_of_mem hi,hv.trans (Nat.le_add_left ..)⟩
lemma cord(l:List α)(h:List β)(hh:h.length=l.length) : Q * extent (Whisk.zone v ∅ h) ≤ extent (Whisk.zone f ∅ l)+2*tube (fun x w=> separation (f x) (g.embed (v w))) l h := by
   let t:=tube (fun x w=> separation (f x) (g.embed (v w))) l h; let W:=Whisk.zone v ∅ h; let d:= extent (Whisk.zone f ∅ l)
   by_cases he:W.Nonempty
   · obtain ⟨j,hj,hQ⟩:= Finset.exists_mem_eq_sup W he fun i=> Finset.sup W (fun j=> separation i j); obtain ⟨k,hk,hP⟩:= Finset.exists_mem_eq_sup W he fun k=> separation j k; have hT:extent (Whisk.zone v ∅ h)=separation j k:= hQ.trans hP; obtain ⟨x,hx,hp⟩:=tang g f v l h hh j hj; obtain ⟨y,hy,hb⟩:=tang g f v l h hh k hk; change _ ≤ d+2*t; rw [hT]
     have hm:Q*separation j k≤_ := Corona.below g j k
     apply hm.trans; have hv:= separation_triangle (g.embed j) x (g.embed k); rw [separation_comm (g.embed j) x] at hv -- may rw both. inspect
     have hL:separation x y ≤ d:=curve hx hy; have hZ:=separation_triangle x y (g.embed k); change _ ≤ t at hp hb; omega
   rw [show extent (Whisk.zone v ∅ h)=0 from ?_]; simp
   unfold extent; change Finset.sup W _=_; rw [show W=∅ from Finset.not_nonempty_iff_eq_empty.mp he];rfl
-- substitute real spread.C formulas
noncomputable def factor(a:ℝ)(p:ℕ)(t:ℝ) := (1+t)^p*Real.exp (a*t)
lemma inc{a x y:ℝ}(p:ℕ)(ha:0≤a)(hx:0≤x)(hh:x≤y):factor a p x ≤factor a p y:=by unfold factor; have h:=hx.trans hh; gcongr
lemma bridge(a x y:ℝ)(p:ℕ)(hx:0 ≤ x)(hy:0≤y):factor a p (x+y)≤factor a p x*factor a p y:=by
   have h:1+(x+y)≤(1+x)*(1+y):=by nlinarith only [mul_nonneg hx hy];
   unfold factor; rw [mul_add,Real.exp_add]
   refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith only [hx,hy]) h _) (by positivity : (0:ℝ) ≤ Real.exp _*Real.exp _)).trans_eq ?_; rw [mul_pow]; ring
lemma sufficient (p:ℕ)(b : ℝ)(h:0 < b): ∃ K:ℝ,1 ≤ K ∧ ∀ t : ℝ,0≤t→(1+t)^p ≤ K*Real.exp (b*t):=by
    let f(t:ℝ):= b*(1+t); have he:Tendsto f atTop atTop:= (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop h
    obtain ⟨m,hm⟩:= eventually_atTop.mp (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp he).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1))); let K:= (1+|m|)^p; have hk:1≤K:=one_le_pow₀ (by linarith only [abs_nonneg m])
    refine ⟨max K (Real.exp b/b^p),hk.trans (le_max_left ..),fun t ht=>?_⟩; let i:=f t; by_cases hh:m≤t
    · have hv:i^p/Real.exp i ≤ 1:=by simpa only [Function.comp_apply, Real.exp_neg,div_eq_mul_inv] using hm t hh
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le); unfold i f at hv; have hp:=div_le_one (Real.exp_pos _)|>.mp hv; rw [mul_pow,mul_add,mul_one,Real.exp_add,mul_comm (b^p)] at hp; rwa [div_mul_eq_mul_div,le_div_iff₀ (pow_pos h p)]
    apply le_trans (b:=K) (show (1+t)^p ≤ K from pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [le_abs_self m,lt_of_not_ge hh]) _); exact (le_max_left ..).trans (le_mul_of_one_le_right (zero_le_one.trans (hk.trans (le_max_left ..))) (Real.one_le_exp (by positivity)))
lemma pressed (a:ℝ)(p:ℕ)(x y:ℝ)(hx:0 ≤ x)(hy:0≤y)(hxy:x+y ≤ 1) : factor a p (x+y) ≤ factor a p 1 ∨ a<0 :=by by_cases he:a<0; exact Or.inr he; exact Or.inl (inc p (not_lt.mp he) (add_nonneg hx hy) hxy)
lemma woven (F:α→β→ℕ)(a:ℝ)(p t:ℕ)(l:List α)(h:List β) : factor a p ((t:ℝ)*(tube F l h:ℝ)/B) ≤beads (fun x y=> factor a p ((t:ℝ)*(F x y:ℝ)/B)) l h:=by
    induction l generalizing h with
    | nil=> simp [beads,tube,factor]
    | cons i l ih=> cases h with
                    | nil=>simp [beads,tube,factor]
                    | cons j h=> simp only [tube, beads,Nat.cast_add, mul_add,add_div]; refine (bridge _ _ _ _ (by positivity) (by positivity)).trans (mul_le_mul_of_nonneg_left (ih h) ?_); unfold factor; positivity
lemma tensile (a:ℝ)(p:ℕ)(ha:0≤a)(l:List α)(h:List β)(hh:h.length=l.length) : spread v ∅ a p h ≤ factor a p ((extent (Whisk.zone f ∅ l):ℝ)/B)*beads (fun x y=> factor a p (2*(separation (f x) (g.embed (v y)):ℝ)/B)) l h:=by
    let d:=extent (Whisk.zone f ∅ l); let X(x : α)(y:β):=separation (f x) (g.embed (v y)); let t:= tube X l h
    have hy:=woven g X a p 2 l h
    have hp : (extent (Whisk.zone v ∅ h):ℝ) ≤ (d:ℝ)/B+2*t/B:=by rw [← add_div,le_div_iff₀ (show 0 < B by positivity),mul_comm]; exact_mod_cast (cord g f v l h hh)
    refine (inc p ha (by positivity) hp).trans ?_; refine (bridge _ _ _ _ (by positivity) (by positivity)).trans (mul_le_mul_of_nonneg_left ?_ (by unfold factor; positivity)); norm_num1 at hy ⊢; exact hy
end
end YM.MSbar.Measuring
