import YM.SchemeRG11.Wolt.Circle
/-! Supply exterior wave from other marked legs. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Wolt
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T:Align.Itinerary}{R r:ℝ}{p q:ℕ → Cover}
local notation "D₁" => Atoll.land G
abbrev liftC(T:Itinerary)(a:Touch G)(m:ℕ)(p:ℕ → Cover):ℕ→ Touch G:=fun i=> (T.gap i)^(-(m+1:ℤ)) • flex (p i) a
def sage(T: Itinerary)(p:ℕ → Cover)(a:Touch G)(m:ℕ): Falls G:= fun i=> (D₁).windfall (liftC T a m p i)
def flagV(s:Fliers)(u:G.ColorIndex)(j:Axis):Touch G := vane0 ((0,j),u) s
lemma flag_leg {s:Fliers}(u:G.ColorIndex)(j:Axis):flagV s u j ∈Stepper G s.card:= ride rfl
lemma driftE (a:Touch G)(p:ℕ → Cover)(u:G.ColorIndex)(j:Axis)(n i:ℕ)(z:Cover)(s:Fliers): fleet s (ribbon (sage T p a n) u i j) z= T.gap i ^ (-(n+1:ℤ))*(D₁).bed (flex (p i-z) a) (flagV s u j):=by
 let F:=sage T p a n; let c:=T.gap i ^(-(n+1:ℤ)); let A:=liftC T a n p i
 have h:sense (F i) (flex z (flagV s u j))=fleet s (ribbon F u i j) z:=by unfold flagV; rw [dip]; simp only [add_zero];rfl
 rw [← h]; change (D₁).bed (c • flex (p i) a) (flex z (flagV s u j))=_; rw [paid_s,commons]
lemma inc_sub(a:ℝ)(r p:Cover): incVec a (r-p)=incVec a r-incVec a p:=by ext i; simp [Full.incVec,mul_sub]
lemma spaceP {y:E4}(hy:Along T p y)(h:2*R < ‖y‖): ∃ c>0,∀ᶠ i in atTop,∀ x, Near T R i x→ c≤ baseU T i (p i-x):=by
 obtain ⟨b,hb,H⟩:= exists_between h
 refine ⟨(b-2*R)/2,by linarith,?_⟩; filter_upwards [(Tendsto.norm hy).eventually (lt_mem_nhds H)] with i hi x hx; let r:=p i; let t:=incVec (T.gap i) r; let u:=incVec (T.gap i) x
 have hv:=cord T i (r-x); rw [inc_sub] at hv; change ‖t-u‖≤ _ at hv; change b< ‖t‖ at hi
 have he:=norm_sub_norm_le t u; have hp: ‖u‖≤ 2*R:= (cord T i x).trans (mul_le_mul_of_nonneg_left hx (by norm_num)); change _ ≤ baseU _ _ (r-_); linarith
lemma intact {a b:Touch G}{y v:E4}(hy:Along T p y)(he:Along T q v)(hp:y≠v)(ha:a∈Stepper G m)(hb:b∈Stepper G n): Finishes (fun i=>(D₁).bed (liftC T a m p i) (liftC T b n q i)):=by
 have h:=(vats ha hb).watch (y-v) (sub_ne_zero.mpr hp) trivial _ (hy.sub he)
 apply h.same; apply Eventually.of_forall; intro i; unfold liftC; dsimp only [view]; rw [paid_s,double_comm (flex (p i) a), paid_s, double_comm (flex _ b), commons,zpow_sub₀ (T.positive _).ne', zpow_neg]; rw [zpow_neg]; ring -- repair
lemma fueled {a b:Touch G}(ha:a∈Stepper G m)(hb:b∈Stepper G n)(_hr:r>0):∃C>0,∀ᶠ i in atTop,∀ x:Cover, r≤ baseU T i x → |(T.gap i)^(-((m:ℤ)+1)-((n:ℤ)+1))*(D₁).bed (flex x a) b| * baseU T i x ^ (((m:ℤ)+1)+(n+1)) ≤ C :=by
 obtain ⟨C,hC,H⟩:= (vats (T:=T) ha hb).wall; refine ⟨C,hC,H.mono (fun i h x hr=> ?_)⟩
 have hx:=T.positive i; have hd:=World.d_pos x; have he:=h x trivial; let V:ℤ:= m+1+(n+1:ℤ); have hV:(-(m+1:ℤ)-(n+1:ℤ))=-V:=by dsimp [V]; omega
 rw [zpow_zero,mul_one,hV] at he; rw [hV,abs_mul,abs_of_pos (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (zpow_pos (mul_pos hx hd) V).le); apply le_of_eq; rw [mul_zpow,zpow_neg,zpow_neg]; field_simp
lemma fires {a:Touch G}{y:E4}(hx:Along T p y)(hv:2*R<‖y‖)(ha:a∈Stepper G m)(hs:Silent a): Blue T R (sage T p a m):=by
 obtain ⟨c,hc,H⟩:=spaceP hx hv
 refine ⟨fun u j s=>?_,fun i=>strikes hx hv a hs _ i,fun u j s w hw y h=>?_⟩
 · let z:ℤ:=(m+1:ℤ)+(s.card+1:ℤ)
   obtain ⟨C,hC,L⟩:=fueled (T:=T) ha (flag_leg (s:=s) u j) hc; refine ⟨C/c^z,div_pos hC (zpow_pos hc _),?_⟩
   filter_upwards [L,H] with i hi hu k hk; let t:=p i-k
   have hp:= T.positive i
   have hZ:z≥0:=by unfold z; omega
   have ht: c≤ baseU T i t:= hu k hk
   unfold dove; rw [driftE, zpow_zero,mul_one]
   let l:=(D₁).bed (flex t a) (flagV s u j)
   have he:|(T.gap i)^(-(m+1:ℤ)-(s.card+1:ℤ))*l|≤ C/c^z:=by
      rw [le_div_iff₀ (zpow_pos hc _)]; exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hZ hc.le ht) (abs_nonneg _)).trans (hi t ht)
   rw [abs_mul,abs_of_pos (zpow_pos hp _)]; rw [abs_mul,abs_of_pos (zpow_pos hp _),zpow_sub₀ hp.ne'] at he
   apply (div_le_iff₀ (zpow_pos hp _)).mp -- check
   calc _ = T.gap i^(-(m+1:ℤ))/T.gap i^(s.card+1:ℤ) * |l| := by ring -- division
        _ ≤ _ := he
 unfold ribbon; -- beware driftE
 let b:= flagV s u j; have heq : ‖w‖ < _:= hw.trans hv
 let L : Sky G 0→ℝ:=0; -- y shadow sequence
 have hi := intact (T:=T) hx h (a:=a) (b:=b) (show _≠_ from by intro e; rw [e] at hv; linarith) ha (flag_leg (s:=s) u j)
 apply hi.same; apply Eventually.of_forall; intro i
 change (D₁).bed _ _ = T.gap i ^ _ * fleet _ (ribbon _ u _ _) _
 rw [driftE, liftC,paid_s,double_comm (flex _ a), liftC,paid_s, double_comm (flex _ b),commons]; ring
lemma salve (i:Key G):Silent (leafProbe 1 i):=fun _=>Pile.within_leg _ _ i
def lensLeg(T: Itinerary)(v: Key G)(p:ℕ → Cover):ℕ→ Touch G:= fun i=>flex (p i) (leafProbe (T.gap i) v)
lemma lens_l(T:Itinerary)(v:Key G)(p:ℕ → Cover)(i:ℕ):lensLeg T v p i=liftC T (leafProbe 1 v) (v.1+1) p i:=by unfold lensLeg leafProbe liftC; rw [map_smul]; simp only [one_zpow,one_smul]; congr 2
lemma legit (a:Key G){y:E4}(h:Along T p y)(hx:2*R<‖y‖):Blue T R (fun i=>(D₁).windfall (lensLeg T a p i)):= by simp_rw [lens_l]; apply fires h hx (high_probe _) (salve a)
end YM.SchemeRG11.Wolt
