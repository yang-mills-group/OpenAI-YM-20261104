import YM.FormalBulk08.Chapel.Buds

/-! Use Newt basis even for small-rank action. Closer to marked branch. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ B C : ℝ}{m r:ℕ}{L : Side}{I J : Type}{T : Tile (edgeL G) (m+1)}(x:edgeL G) (t : chain (Stationary.Loc G 1) m)

def spin_at (i:Fin m) (T:Tile (edgeL G) (m+1)) : Tile (edgeL G) (m+1):=fun v=>tap T (v ∘ Equiv.swap i.succ 0)
lemma dollars_at (u:Fin m)(x:edgeL G)(t:chain (Stationary.Loc G 1) m)(w:cloud m)(h:Agate T):
   let i:=(t u).2
   rowC (spin_at u T) x t w=∑ k:Axis,(rowC T x (update t u (coord k,i)) w-rowC T x (update t u (coord k,i)) (w-buzz (u,k))) := by
    let a : chain (edgeL G) (m+1):= Fin.cons x (snake x.1 t w); let s:= Equiv.swap u.succ 0; let P:= a ∘ s;intro i;let b:= (P 0).1
    have H:P 0=(snake x.1 t w u):= by simp [P,s,a]
    have hz: (P 0).2.2=i:= congr_arg (fun m:edgeL G=>m.2.2) H
    change riverP _ b T (Fin.tail P)=_; rw [show (P 0).2.2=i from hz];unfold riverP; simp_rw [Finset.sum_apply,Pi.sub_apply];symm; refine Fintype.sum_equiv axisEquiv _ _ fun k=>?_
    let Q : chain (edgeL G) m:=Fin.tail P
    have ha (d : Cover) (v: cloud m) (hy: x.1+rack v u=d)(hp:∀ j,j≠u→ rack v j=rack w j) :
         shed T (show edgeL G from (d,axisEquiv k,i)) Q= rowC T x (update t u (coord k,i)) v := by
       let c:= update t u (coord k,i); let S:chain _ (m+1):= Fin.cons x (snake x.1 c v)
       apply Eq.trans ?_ (h S s); unfold Lava.shed; apply congr_arg T; ext1 j
       cases j using Fin.cases with
       | zero=> simp [s,S,snake,hy,c]
       | succ j=>
         by_cases he:j=u
         · subst j; simp [Q,P,s,a,S,Fin.tail]
         have h' : j.succ≠u.succ:= fun g=> he (Fin.succ_injective _ g)
         simp [a,S,c,Q,P,Fin.tail,s,Equiv.swap_apply_of_ne_of_ne h' (Fin.succ_ne_zero _),snake,hp j he,he]
    congr 1; exact (ha b w (congr_arg Prod.fst H).symm fun _ _=> rfl).symm
    have he (j): rack w j=rack (w-buzz (u,k)) j+(if u=j then step k else 0):= by
        conv_lhs=> rw [←sub_add_cancel w (buzz (u,k)),rack_plus]
        split_ifs <;> simp
    apply Eq.symm; apply ha (backwards b (axisEquiv k)) (w-buzz (u,k)); unfold b;rw [H]; change x.1+rack _ _= backwards (x.1+rack w u) _;rw [he u,backwards,axisEquiv.symm_apply_apply,if_pos rfl]; abel
    intro j hj; exact Eq.symm (by simpa only [if_neg (Ne.symm hj),add_zero] using he j)

def piles (T:Tile (Biglot I) (m+1))(x:Biglot I)(t:chain I m)(p:Grades (Fin m × Axis)):=∑' w,rowC T x t w* hat p w
lemma kroner (u:Fin m)(p : Grades (Fin m × Axis))(hu:∀ a,p (u,a)=0)(h:Agate T)(H:Bail (fame _) σ T C)(hs:0<σ):
     let a:= axisEquiv.symm (t u).1
     ∑' w,rowC (spin_at u T) x t w * (curveW (u,a) w*hat p w)= -piles T x t p:= by
    let f:= curveW (u,axisEquiv.symm (t u).1)*hat p; intro a;let i:=(t u).2; let S k z:=rowC T x (update t u (coord k,i)) z; have hf: Par f:=par_mul (par_curve _) (par_hat p)
    have he k w : f (w+buzz (u,k))= f w + if a=k then hat p w else 0 := by
        have hp:hat p (w+buzz (u,k))=hat p w:=hat_dead p (u,k) (hu _) _
        change curveW (u,a) _ * _ = curveW (u,a) _ * _+_; rw [hp]; by_cases hi:a=k <;> simp [hi,curveW,buzz, add_mul]
    have hp k : Summable (fun w => S k w * f w):= summableRow hs hf H x _
    have hh k : Summable (fun w=>S k (w-buzz (u,k))*f w):= by
       let e :=Equiv.addRight (buzz (u,k));apply (Equiv.summable_iff e).mp; refine (summableRow hs (par_shift hf (buzz (u,k))) H x (update t u (coord k,i))).congr fun w=> ?_; simp [e,S]
    have hD k : ∑' w,(S k w * f w - S k (w-buzz (u,k))*f w) = if k=a then -piles T x t p else 0 := by
       rw [(hp k).tsum_sub (hh k),←Equiv.tsum_eq (Equiv.addRight (buzz (u,k))) (fun w=> S k (w-buzz (u,k))* f w)]; simp_rw [show ∀ (x: Wand (Fin m×Axis)) b,Equiv.addRight x b=b+x from fun _ _=>rfl,add_sub_cancel_right,he k]
       by_cases h:k=a
       · rw [h,if_pos rfl]; simp_rw [mul_add]; rw [(hp a).tsum_add]; swap; · exact summableRow hs (par_hat p) H x _
         rw [sub_add_cancel_left]; unfold S a i -- binder issues update id
         rw [show update t u _= t from ?_];rfl
         rw [show (coord _,(t u).2)=t u from Prod.ext (axisEquiv.apply_symm_apply _) rfl]; exact Function.update_eq_self ..
       simp [h,Ne.symm h]
    change (∑' w,rowC (spin_at u T) x t w*f w)= _; simp_rw [dollars_at u x t _ h]; change (∑' w,(∑ k:Axis,(S k w-S k (w-buzz (u,k))))* f w)= _; simp_rw [Finset.sum_mul,sub_mul,Summable.tsum_finsetSum (fun k _=>(hp k).sub (hh k)),hD];simp
lemma untouched (p: Grades (Fin m×Axis))(h: upper p<m):∃ i,∀ j:Axis,p (i,j)=0 := by
    by_contra! hh
    have hp:m≤ upper p := by unfold upper;rw [Fintype.sum_prod_type]; apply le_trans (b:=∑ i:Fin m, 1) (by simp) (Finset.sum_le_sum ?_); intro i _; obtain ⟨k,hk⟩:= hh i;exact (Nat.pos_of_ne_zero hk).trans_le (Finset.single_le_sum (f:=fun k=>p (i,k)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k))
    omega

lemma route_price (p: Grades (Fin m× Axis))(hs:0<σ)(h:upper p<m)(G:Gauge): ∃ K:ℝ,0<K∧∀ x t' (T: Tile (edgeL G) (m+1)), Agate T→ ∀ B,Bail (fame _) σ (tap T) B→ ∀ C,Bail (fame _) σ T C → |piles T x t' p| ≤ K*B:= by
   obtain ⟨u,hu⟩:= untouched p h
   choose F hF H using fun i:Axis=> costs_rowC hs (par_mul (par_curve (u,i)) (par_hat p)) (Stationary.Loc G 1); let J:= ∑ i,F i
   refine ⟨max 1 J,lt_max_of_lt_left one_pos, fun x t T hh B hb C hc=>?_⟩
   let a:= axisEquiv.symm (t u).1; have he := kroner x t u p hu hh hc hs
   have hv := H a B (spin_at u T) x t (hb.spins _)
   refine le_trans (b:= F a*B) ?_ (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (f:=F) (fun i _=>hF i) (Finset.mem_univ a)).trans (le_max_right ..)) hb.1); apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hF a) hb.1)).mp; rw [←abs_neg,←he,←Real.norm_eq_abs,ofReal_norm]; exact enorm_tsum_le_tsum_enorm.trans hv
end YM.FormalBulk08.Chapel
