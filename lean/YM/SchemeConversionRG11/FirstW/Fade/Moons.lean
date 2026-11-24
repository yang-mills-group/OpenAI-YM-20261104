import YM.SchemeConversionRG11.FirstW.Fade.Ports
import YM.SchemeConversionRG11.FirstW.Fold.Partition
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{o p q:StepPath T} {A B C:Sight T G}
def verdant (T:Itinerary)(x:StepPath T)(k:Labels.Key G): Sight T G:= fun i=> river (T.gap i) k (x i)
def farlap (T:Itinerary)(P:Hall T ℝ)(A B C: Sight T G)(i:ℕ):= ∑ x:Site (T.period i),P i x* ∑ a:Ticket,∑ b:Ticket,tower G x (icon (fresh a) (fresh b)) (A i) (B i) (C i)
lemma near_wheel (Q:Wash) (s:StepPath T): ∀ᶠ i in atTop, wheelS G T i Q (terms (s i) (A i)) (terms (s i) (B i)) (terms (s i) (C i))= farlap T (Mask T s Q) A B C i := by
 let f(i:ℕ)(x: Cover):= soft Q (Moss T i x)*∑ a:Ticket,∑ b:Ticket,tower G x (icon (fresh a) (fresh b)) (terms (s i) (A i)) (terms (s i) (B i)) (terms (s i) (C i))
 have he:Lives T Q.rOut f := Eventually.of_forall fun i x hx=> by by_contra h; exact hx (by unfold f; rw [soft_life Q _ (le_of_lt (lt_of_not_ge h)),zero_mul])
 filter_upwards [stackV T Q.rOut f he] with i hi; rw [wash_eq,show (∑ _x∈pod T Q.rOut i, _)= expenditure T f i from hi.symm]; unfold farlap; let P:=Mask T s Q; let g(x:Site (T.period i)):= P i x* ∑ a:Ticket,∑ b:Ticket,tower G x (icon (fresh a) (fresh b)) (A i) (B i) (C i); change expenditure T f i=∑ x,g x; rw [← Equiv.sum_comp (Equiv.addRight (s i)) g]; apply Finset.sum_congr rfl; intro x _; change f i (lift x)=g (x+s i); simp only [f,g,P,Mask,out,tower_wrap,wrap_lift, add_sub_cancel_right]
lemma orbits (i:ℕ): farlap T 1 A B C i= lapSky G (T.period i) (A i) (B i) (C i):= by simp only [farlap,lap_shield,Pi.one_apply,one_mul,wheels]
lemma coast (P:Hall T ℝ)(s:StepPath T): farlap T (resiteR T P s) (passA T s A) (passA T s B) (passA T s C)= farlap T P A B C:= by funext i; unfold farlap; simp only [passA,resiteR,tower_translate]; exact Equiv.sum_comp (Equiv.addRight (s i)) (fun x:Site (T.period i)=>P i x* ∑ a:Ticket,∑ b:Ticket,tower G x (icon (fresh a) (fresh b)) (A i) (B i) (C i))
lemma move_ver (x y:StepPath T)(a:Labels.Key G): passA T x (verdant T y a)=verdant T (y-x) a:= by funext i; unfold passA verdant river; rw [map_smul,consumes]; rfl
lemma farlap_paid {x y z: StepPath T}{a b c:Labels.Key G}{P:Hall T ℝ} (h:∀ i j:Step,Helen (CrestBill T (SeaA T a x) (SeaA T b y) (SeaA T c z) i j P)): Helen (farlap T P (verdant T x a) (verdant T y b) (verdant T z c)):= by
 have hp(a:Labels.Key G)(x:StepPath T)(i:ℕ): verdant T x a i=T.gap i • SeaA T a x i:= Eq.symm (smul_inv_smul₀ (T.positive i|>.ne') _)
 let f(i j:Ticket):=CrestBill T (SeaA T a x) (SeaA T b y) (SeaA T c z) (fresh i) (fresh j) P
 convert! (collectH Finset.univ (fun i:Ticket=> fun k=> ∑ j,f i j k) fun i hi=>collectH _ (f i) (fun _ _=>h _ _)) using 1
 funext i; unfold farlap f CrestBill; simp_rw [hp,loadD, Finset.mul_sum]; rw [Finset.sum_comm]; conv_lhs=> arg 2; intro b; rw [Finset.sum_comm]
 apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; exact Finset.sum_congr rfl fun j _=>mul_left_comm ..
variable {r:ℕ} {w:Points r}{u:∀ i,Full.Grid (T.period i) r} {R:ℝ}{Q:Wash} {a b e:At G r 6}
def crossQ (T:Itinerary)(A B C: Sight T G)(Q:Wash)(s:StepPath T)(i:ℕ):= lapSky G (T.period i) (A i) (B i) (C i) - deckP _ (s i) (wheelS G T i Q) (A i) (B i) (C i)
def forth (T:Itinerary)(o:∀ i,Full.Grid (T.period i) r)(a:At G r 6): Sight T G:= fun i=> arise (T.gap i) (o i) a
lemma sea_point (T:Itinerary)(o:∀ i,Full.Grid (T.period i) r)(a:At G r 6): forth T o a=verdant T (fun i=> o i a.1) a.2.val:= rfl
lemma crossQ_print (T:Itinerary)(A B C: Sight T G)(Q:Wash)(s:StepPath T): crossQ T A B C Q s =ᶠ[atTop] farlap T (1-Mask T s Q) A B C := by
 filter_upwards [near_wheel (T:=T) (A:=A) (B:=B) (C:=C) Q s] with i hi
 rw [crossQ,show deckP _ (s i) (wheelS G T i Q) (A i) (B i) (C i) = farlap T (Mask T s Q) A B C i from hi,←orbits]; unfold farlap; simp_rw [Pi.sub_apply,sub_mul, Finset.sum_sub_distrib]
lemma upkeep (Q:Wash)(d:Diorama T u w)(s:Fin r)(a b:Who G 6)(hP:R<‖w s-w e.1‖)(hQ:Q.rOut<R)(hc:MarkGrid T c): Helen (crossQ T (forth T u (s,a)) (forth T u (s,b)) (forth T u e) Q (fun i=>u i s)) := by
 let f(i:ℕ):= u i s; let g(i:ℕ):= u i e.1
 obtain ⟨z,H⟩:= (show Helen (farlap T (1-Mask T f Q) (forth T u (s,a)) (forth T u (s,b)) (forth T u e)) from by
    rw [←coast _ f,sea_point,sea_point,sea_point]; simp_rw [move_ver]; rw [show resiteR T _ f= 1-Mask T 0 Q from by rw [show Mask T 0 Q=resiteR T (Mask T f Q) f from by rw [resite_mask,sub_self]]; rfl]
    change Helen (farlap T _ (verdant T (f-f) a.val) (verdant T (f-f) b.val) (verdant T (g-f) _)); rw [sub_self]; apply farlap_paid; intro i j; apply border Q Q i j (x:=0) sails_zero (looked d s e.1) hc hQ; simpa using hP)
 exact ⟨_,H.congr' (crossQ_print T _ _ _ Q f).symm⟩
lemma verb_kept (Q:Wash)(d:Diorama T u w)(h₁:R<‖w b.1-w a.1‖)(h₂:R<‖w e.1-w a.1‖)(h₃:R<‖w e.1-w b.1‖)(hq:Q.rOut<R)(hc:MarkGrid T c): Helen (fun i=> lapSky G (T.period i) (forth T u a i) (forth T u b i) (forth T u e i)):= by
 simp_rw [←orbits]; let x(i:ℕ):= u i a.1; rw [← show farlap T _ _ _ _ = farlap T 1 (forth T u a) (forth T u b) (forth T u e) from coast _ x]; simp_rw [sea_point,move_ver]; rw [show ((fun i=>u i a.fst)-x)=0 from sub_self x]; change Helen (farlap T 1 _ _ _); apply farlap_paid; intro i j
 apply liner Q i j (x:=0) sails_zero (looked d a.1 b.1) (looked d a.1 e.1) hc hq <;> simpa
lemma path_paid (p:Players G r 6)(d:Diorama T u w)(hq:Q.rOut<R)(hc:MarkGrid T c)(hx:∀ i j:Fin r,i≠ j → R<‖w i-w j‖): Helen (fun i=> flowV p (u i) (T.gap i)) ∧ ∀ s:Fin r,Helen (fun i=> morn p (u i) (T.gap i) s (currents Q T u s i)) := by
 have hl(p:Players G r 6): Helen (fun i=> ZeroR (u i) (T.gap i) p):= ⟨_,Warp.poly_limit 6 T _ _ d.ht d.hs d.hdiv (fun i=>uncap_height (p i))⟩
 constructor
 · unfold flowV; apply collectH; intro a _; apply collectH; intro b hb; apply collectH; intro e he
   have he':= Finset.mem_inter.mp he; obtain ⟨v,hv⟩:= verb_kept Q d (a:=a) (b:=b) (e:=e) (hx _ _ (Finset.mem_filter.mp hb).2) (hx _ _ (Finset.mem_filter.mp he'.1).2) (hx _ _ (Finset.mem_filter.mp he'.2).2) hq hc
   obtain ⟨y,hy⟩:=hl (dict e (dict b (dict a p))); exact ⟨_,(Complex.continuous_ofReal.continuousAt.tendsto.comp hv).mul hy⟩
 intro s; unfold morn; apply collectH; intro a _; apply collectH; intro b _; apply collectH; intro e he
 obtain ⟨v,hv⟩:= upkeep Q d s a b (e:=e) (hx _ _ (Finset.mem_filter.mp he).2.symm) hq hc; obtain ⟨z,Z⟩:= hl (dict e (dict (s,b) (dict (s,a) p))); simp_rw [verbD,stagedV,← sub_mul,←Complex.ofReal_sub]
 exact ⟨_, ((Complex.continuous_ofReal.continuousAt.tendsto.comp hv).mul Z).const_mul 3⟩
end YM.RG11.FirstW.Deck
