import YM.WilsonCoeffUV.Reclosure.RayNull
/-!
# Vacuum Laurent to torus via relative slots. No supplied winding estimate
assumed. Use this only at fixed positive correlation displacements (Lift equality),
independent of readout. Sym copies replicated around anchor, not renormalized
by period. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}
variable {F:post G t}{s A:ℝ}

abbrev stars (G:Gauge)(t:ℕ)(n:Side):= Fin (t+1) → Co n (Hooks G)
abbrev stH (X:stars G t c): Haze G (t+1):=fun i=>(X i).2.2
abbrev stR (X:stars G t c): Run (t+1):=fun i=>(X i).2.1

def trope (X:stars G t c)(w : Shift (Keys t)): Prop:=∀ i,(X i).1-(X 0).1 = wrap c (feetP w i)
open Classical in
def flair (X:stars G t c)(F:post G t)(w:Shift (Keys t)): ℝ := if trope X w then plantern F (stH X) (stR X) w else 0

def lagoon (F:post G t) (n: Side) : Ten ℝ (Co n (Hooks G)) (t+1):=fun X=>∑' w, flair X F w
lemma flair_hit {X : stars G t c}{w}(h:trope X w): flair X F w=plantern F (stH X) (stR X) w:= if_pos h
lemma flair_miss {X:stars G t c}{w} (h:¬ trope X w) : flair X F w=0:= if_neg h
lemma flair_cost (h:Amber terrain s A F)(hp:0<s)(x:stars G t c): Width (hingeZ s t) (A*hinges s t) (flair x F):=by
    have ht:= wages h hp (stH x) (stR x)
    apply budget_minor ht (fun i=>by positivity); intro i; apply mul_le_mul_of_nonneg_left _ (by positivity); by_cases he:trope x i
    · rw [flair_hit he, Complex.norm_real]
    rw [flair_miss he,norm_zero]; positivity
-- prices x displacement covers any shift ingredient. each |offset| ≤ size w.
lemma measure_foot (w: Shift (Keys t))(i: Fin (t+1)): size (feetP w i)≤ size w:= by
   refine Fin.cases ?_ (fun i=>?_) i; · simp [feetP,Laurent.size]
   unfold Laurent.size; rw [Fintype.sum_prod_type]; exact Finset.single_le_sum (a:=i) (f:=fun j :Fin t=>∑ b:Axis,(w (j,b)).natAbs) (fun j _=>by positivity) (Finset.mem_univ _)
lemma billing {X:stars G t c}{w:Shift (Keys t)} (p:trope X w): soar (tor c) X≤2*size w:= by
    apply league_le; intro i j; change size (lift ((X j).1-(X i).1))≤ _
    rw [show _-_= _ from (show (X j).1-(X i).1=wrap c (feetP w j-feetP w i) by rw [map_sub,← p j,← p i]; abel)]; refine (wrap_size ..).trans ?_; rw [sub_eq_add_neg]; apply le_trans (size_add ..); rw [size_neg]; have h:=measure_foot w i; have t:=measure_foot w j; omega
lemma lagoon_cost (h:Amber terrain s A F)(hp:0<s)(n:Side): Amber (tor n) (hingeZ s t/2) (A*hinges s t) (lagoon F n):=by
    let a:=hingeZ s t; let B:=A*hinges s t
    have he :0 ≤ B:= mul_nonneg h.1 (hinge_reserve hp _).le
    have hx:0<a:= hinge_paid hp t
    refine ⟨he,fun X=>?_⟩; let F':=flair X F
    let l:=soar (tor n) X
    let u:=Real.exp (-(a/2)*l)
    have hu:0≤u:=by unfold u; positivity
    have ht: Width a B F':=flair_cost h hp X
    have hg:= (ht.unweighted hx.le).2.1
    have H w: ‖F' w‖≤ (Real.exp (a*size w)* ‖F' w‖)*u := by
       rw [mul_right_comm]; by_cases hf:trope X w; swap; · simp [F',flair_miss hf]
       apply le_mul_of_one_le_left (norm_nonneg _); unfold u; rw [← Real.exp_add]; refine Real.one_le_exp ?_
       have hb : (l:ℝ)≤ 2*size w:=by exact_mod_cast billing hf
       nlinarith
    have hr:= ht.2.1.mul_right u
    exact (norm_tsum_le_tsum_norm hg).trans ((hg.tsum_le_tsum H hr).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 hu))
lemma lagoon_walk (F:post G t)(n:Side): stroll (lagoon F n):=by
   intro i x; apply tsum_congr; intro j; have he : trope (jog i ∘ x) j ↔ trope x j:=by
      unfold trope; change (∀ j',(i+(x j').1)-(i+(x 0).1)=_ )↔_; simp
   by_cases h:trope x j; · rw [flair_hit (he.mpr h), flair_hit h]; rfl
   rw [flair_miss h, flair_miss (mt he.mp h)]

-- permutation lift

def whirlP (S:Equiv.Perm (Fin (t+1)))(w:Shift (Keys t)): Shift (Keys t) := fun i=>(feetP w (S i.1.succ)-feetP w (S 0)) i.2
lemma whirl_sole (S:Equiv.Perm (Fin (t+1)))(w:Shift (Keys t)) i: feetP (whirlP S w) i=feetP w (S i)-feetP w (S 0):= by refine Fin.cases (by simp [feetP,sub_self]) (fun i=>?_) i; rw [feetP,Fin.cons_succ]; rfl
lemma undoWh (S:Equiv.Perm (Fin (t+1)))(w:Shift (Keys t)): whirlP S.symm (whirlP S w)=w:=by
   ext1 ⟨i,j⟩
   rw [whirlP,whirl_sole,whirl_sole]; simp [feetP]
def whQ (S:Equiv.Perm (Fin (t+1))): Equiv.Perm (Shift (Keys t)):=⟨whirlP S,whirlP S.symm,undoWh S,undoWh S.symm⟩
lemma trope_whirl {t:ℕ}(x:stars G t c)(S:Equiv.Perm (Fin (t+1)))(w)(p:trope x w): trope (x ∘ S) (whirlP S w):=by
   intro i; rw [whirl_sole,map_sub,← p,←p]; abel
lemma trail_whirl (F:post G t)(h:Blue.Smooth F)(p:stroll F)(z:stars G t c)(S:Equiv.Perm (Fin (t+1)))(x) : flair (z ∘ S) F (whirlP S x)= flair z F x:=by
   by_cases he:trope z x
   · rw [flair_hit he,flair_hit (trope_whirl z S x he)]; unfold plantern; let u:=-feetP x (S 0); let W:= goose x (stH z) (stR z) ∘ S
     have hx : goose (whirlP S x) (stH (z ∘ S)) (stR (z ∘ S))=jog u ∘ W:=by
        funext i; apply Prod.ext _ _
        · change feetP _ _=u+feetP x _
          rw [whirl_sole,sub_eq_add_neg, add_comm]
        rfl
     rw [hx,p]; exact h S _
   rw [flair_miss he,flair_miss]; intro hp; have ht := trope_whirl _ S.symm _ hp; simp_rw [undoWh,Function.comp_assoc,Equiv.self_comp_symm,comp_id] at ht; exact he ht
lemma lagoon_smooth (F:post G t)(h:Blue.Smooth F)(p:stroll F)(n:Side): Blue.Smooth (lagoon F n):= by
   intro s x; unfold lagoon; rw [← (whQ s).tsum_eq (flair (x ∘ s) F)]; exact tsum_congr fun j=>trail_whirl F h p x s j
-- limit on all dims through Side at top. mask.
def salvo (x:Fin (t+1)→YForest G): Shift (Keys t):= fun i=> ((x i.1.succ).1-(x 0).1) i.2
lemma sole_salvo (x:Fin (t+1)→YForest G)(i): feetP (salvo x) i= (x i).1-(x 0).1:= by refine Fin.cases (by simp [feetP]) (fun i=>?_) i; rw [feetP,Fin.cons_succ]; rfl
lemma sole_right (x:Fin (t+1)→YForest G): trope (foldUnder c ∘ x) (salvo x) := by intro i; rw [sole_salvo,map_sub]; rfl
lemma lagoon_yields (h:Amber terrain s A F)(he:0<s)(hu:stroll F): Yields (lagoon F) F:=by
   have hp:0<hingeZ s t/2:=by apply div_pos (hinge_paid he _); norm_num
   refine ⟨fun x=>?_, Eventually.of_forall fun n=>lagoon_walk F n,_,_,hp,Eventually.of_forall fun n=>lagoon_cost h he n⟩
   simp only [dilute,Nat.succ_ne_zero,↓reduceIte]
   let I j:=(x j).2.2; let J j :=(x j).2.1
   let P n:= flair (foldUnder n ∘ x) F; let Q i:= if i=salvo x then F x else 0
   have hB:= wages h he I J
   let B i:= ‖plantern F I J i‖
   have hK: Summable B:= by simpa only [Complex.norm_real] using (hB.unweighted (hinge_paid he _).le).2.1
   have hx:∀ n i,‖P n i‖≤B i:=by
      intro n i; by_cases hv: trope (foldUnder n ∘ x) i
      · unfold P; rw [flair_hit hv]; exact le_rfl
      unfold P B; rw [flair_miss hv,norm_zero]; positivity
   have hD :∑' i,Q i=F x:=by unfold Q; rw [tsum_ite_eq]
   have hz i:Tendsto (fun n=>P n i) atTop (𝓝 (Q i)):=by
      by_cases w:i=salvo x
      · subst i; refine tendsto_const_nhds.congr (fun n=>?_);  unfold Q P; rw [flair_hit (sole_right x), if_pos rfl,plantern]; symm
        refine (congr_arg F ?_).trans (hu (-(x 0).1) x); ext1 i; refine Prod.ext ?_ rfl; change feetP _ _=-(x 0).1+_
        rw [sole_salvo,sub_eq_add_neg,add_comm]
      apply tendsto_const_nhds.congr';
      filter_upwards [eventually_all.mpr (fun j :Fin (t+1)=>lift_ready ((x j).1-(x 0).1)),eventually_all.mpr (fun j:Fin (t+1)=>lift_ready (feetP i j))] with n ha hb
      unfold Q P; rw [if_neg w,flair_miss]; intro h; apply w; funext ⟨p,j⟩; have h : lift (wrap n ((x p.succ).1-(x 0).1))=lift (wrap n (feetP i p.succ)):= by rw [map_sub]; exact congr_arg lift (h p.succ)
      rw [ha,hb,feetP,Fin.cons_succ] at h; exact congr_fun h.symm j
   conv_rhs=> rw [←hD]
   exact tendsto_tsum_of_dominated_convergence hK hz (Eventually.of_forall hx)
end YM.WilsonCoeffUV.Bank.Mosaic
