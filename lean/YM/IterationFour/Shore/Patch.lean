import YM.IterationFour.Shore.Aster

set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.IterationFour
open Lattice Wilson RG Function MeasureTheory Filter Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
open Quad Work Tensor Next.Fluctuations
attribute [local instance] Gauge.frobInner
variable {G : Gauge}{n : Side}{p : BudgetPoint}{f : G.Mat→ℝ}{q :ℕ}
namespace Stamp
variable (h:Stamp (G:=G) f q)
include h
lemma smooth (x:Cell n)(U:Config G n): ContDiff ℝ ω (element G f x ∘ increment U):= h.globalB.comp (mat_face_inc ..)
lemma regular (x:Cell n)(p:BudgetPoint): p.Regular (touched x) (element G f x):=by
   have hv(U : Config G n):= ((h.smooth x U).of_le (m:=(p.order:ℕ∞)) le_top |>.contDiffAt (x:=0))
   refine ⟨fun _ _ hh=>congr_arg (f ∘ G.mat) (face_local x _ _ hh),Continuous.measurable (h.globalB.continuous.comp (G.continuous_mat.comp (continuous_travel ..))),fun k U=>?_,fun U _=>hv U,fun U _ a l hl=> Next.Foundations.left_has a hl (hv U)⟩
   exact ((congr_arg (f ∘ G.mat) (face_gauge k U x))).trans (h.conjugate ..)
lemma flat (x:Cell n): FlatAt q (element G f x ∘ increment (1: Config G n)) 0:= by
    refine h.cancels _ (fun v=>faceValue (increment 1 v) x) (mat_face_inc ..|>.contDiffAt) ?_
    rw [Work.G07.at_zero_increment,face_one]
lemma turns (x:Cell n) (s:Signed) (b:Site n) (U:Config G n):element G f (Face.send s b x) U= element G f x (pull s b U):=
  (Face.send_price U x s b (f ∘ G.mat) h.reverse (fun v u=>h.conjugate u v)).symm
omit h in
lemma same_jet (p:Cell n)(U:Config G n)(l:List (Directions G n)): leftDerivs (element G f p) l U=lamp f (l.map (· ∘ edges p)) (mat (U ∘ edges p)):=by
   induction l generalizing U with
   | nil => rw [List.map_nil,lamp,comp_apply,read_actual,read_edges]; rfl
   | cons a l ih=> simp only [leftDerivs, List.map_cons, ih, lamp]; exact congr_arg (deriv · 0) (funext fun t => congr_arg _ (funext fun i : Fin 4=> G.mat_mul ..))
lemma rated (k P:ℕ):∃ C δ:ℝ,0<C∧ 0<δ∧δ≤1∧ ∀b:BudgetPoint, b.power=P→b.order=k→b.threshold ≤ δ → ∀ (n:Side)(p:Cell n)(o:Site n), o∈ touched p → b.supBounds o (touched p) (element G f p) (C*b.threshold^q):=by
   let J:=Fin (k+1)
   choose c d hc hd h' h using fun i : J => collected h i.val ((1+4)^P)
   obtain ⟨i,hi,he⟩:= Finset.exists_min_image Finset.univ d Finset.univ_nonempty
   let C:=∑ j:J,c j
   have hC:0<C:= Finset.sum_pos (fun i _=> hc i) Finset.univ_nonempty
   refine ⟨C,d i,hC, hd i,h' i, fun b hb hk ht n p o ho=>?_⟩ --
   refine ⟨mul_nonneg hC.le (pow_nonneg b.threshold_pos.le _),?_⟩; intro U hu l hl hA
   have hL: l.length < k+1:= Nat.lt_succ_of_le (hl.trans_eq hk); let j:J:=⟨l.length,hL⟩; let a(t:Fin j.val):=l.get t ∘ edges p
   have ha: ‖a‖ ≤ b.threshold*(1+4:ℝ)^P:=by
     have hh:=b.threshold_pos
     apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro t; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro m
     apply ((hA _ (l.get_mem t)) (edges p m)).trans
     rw [hb]; gcongr; exact_mod_cast (separation_triangle (edges p m).1 p.1 o).trans (Nat.add_le_add (visit_near p (edges_visit p m)) ((separation_comm _ _) ▸ visit_near p ho))
   have H:= h j a (U ∘ edges p) _ b.threshold_pos (ht.trans (he j (Finset.mem_univ j))) ha ((read_edges p U).symm ▸ healthy_chord p U hu)
   have hz : c j ≤ C:= Finset.single_le_sum (fun i _=> (hc i).le) (Finset.mem_univ j)
   rw [same_jet, ← show List.ofFn a = l.map (· ∘ edges p) from (List.map_ofFn (g:=(· ∘ edges p)) (f:=l.get)).symm.trans (by rw [List.ofFn_get])]
   exact H.trans (mul_le_mul_of_nonneg_right hz (pow_nonneg b.threshold_pos.le _))

def cost (S:Stage):= (h.rated S.order S.power).choose
def near (S:Stage):= (h.rated S.order S.power).choose_spec.choose
lemma history (S:Stage): 0<h.cost S∧0<h.near S:= ⟨(h.rated S.order S.power).choose_spec.choose_spec.1,(h.rated S.order S.power).choose_spec.choose_spec.2.1⟩
end Stamp
open Start Padded YM.IterationFour.Vacuum

variable (n G)
def slate (v:ℝ) (f:G.Mat→ℝ): Payload G n := ⟨eInfo∘name (Sheet n),fun i=> if fixed (Sheet n) i then (name (Sheet n) i).elim (fun u=> v • element G f u.positive) (fun _=>0) else 0⟩
variable {G n}
variable (h:Stamp (G:=G) f q)
lemma tally (u :ℝ)(U:Config G n): (slate G n u f).amount p U=u *∑ i:Key n, masked p.threshold i.skin (element G f i.positive) U := by
   let φ (i:Sheet n):=(masked p.threshold (eInfo i).support (i.elim (fun j=> u • element G f j.positive) (fun _=>0)) U)
   unfold Payload.amount; rw [Padded.totals (α:=Sheet n) (g:=φ) (fun i=>?_)]
   · rw [Fintype.sum_sum_type,sum_eq_zero (s:=univ) (f:=fun j=> φ (.inr j)) (fun j _=> (Start.masked_zero ..)), add_zero,mul_sum]; refine sum_congr rfl fun i _=> ?_
     exact AnalyticBridge.VerifiedReset.Collection.mask_mul ..
   unfold slate; dsimp only [comp_apply]; split; rfl; exact Start.masked_zero ..
def eyeG (S:Stage) :ℝ:= (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes* Real.exp (S.supportExponent*5^4)
lemma leaf (h : Stamp (G:=G) f q) (hq:2<q) (S:Stage) (hs:S.order=p.order) (hp:S.power=p.power) (hS:S.supportExponent=p.supportExponent) (u:ℝ) (hz:p.threshold ≤ h.near S) :
    (slate G n u f).Invoice p (eyeG S * (|u| * (h.cost S*p.threshold^q))):= by
   let B:=slate G n u f; let P:=∑ i:Axis,i.val
   let s:=h.cost S*p.threshold^q; let κ:= ‖u‖*s
   have hb:0 ≤ κ:=mul_nonneg (norm_nonneg _) (mul_nonneg (h.history S|>.1.le) (pow_nonneg p.threshold_pos.le _))
   let E :=fun i:Sheet n=> i.elim (fun _=>κ) (fun _=> (0:ℝ)); let T:=fun i:ℕ=> if fixed (Sheet n) i then E (name (Sheet n) i) else 0
   have hv : ∀ i, p.Regular (B.labels i).support (B.action i) ∧ B.action i 1=0 ∧ (∀ x y, logHessian (B.action i) x y=0) ∧ p.supBounds (B.labels i).site (B.labels i).support (B.action i) (T i):= by
     intro i; unfold B slate T; dsimp only; split
     next hn=>
       dsimp only [comp_apply]; cases name (Sheet n) i with
       | inl m =>
            change p.Regular m.skin _ ∧ (u • element G f m.positive) _=0 ∧ (∀ x y, logHessian (u•element G f m.positive) x y=0) ∧ p.supBounds m.native m.skin _ κ
            have hv:= h.flat m.positive; let g:=element G f m.positive
            rw [m.skin_positive]; refine ⟨Start.times_reg u (h.regular ..),?_,fun x y=>?_,Start.times_bound u ((h.rated S.order S.power).choose_spec.choose_spec.2.2.2 p hp.symm hs.symm hz _ _ _ (m.skin_positive ▸ m.native_mem))⟩
            · have hl:= congr_arg (Tensor.diagonal · (0:Directions G n)) (hv 0 (by omega)); have hz:g 1=0:= by simpa [Tensor.diagonal,comp_def,g,G07.at_zero_increment] using hl
              change u*g 1=0; rw [hz,mul_zero]
            change iteratedFDeriv ℝ 2 (u • (g ∘ increment 1)) 0 ![x,y] = 0
            rw [iteratedFDeriv_const_smul_apply ((h.smooth ..).contDiffAt.of_le le_top),show iteratedFDeriv ℝ 2 (g ∘ increment 1) 0=0 from hv 2 hq,smul_zero]; rfl
       | inr m=>
            change p.Regular _ 0 ∧ 0=0 ∧ (∀ x y, logHessian 0 x y=0)∧ p.supBounds _ _ _ 0
            exact ⟨Start.zero_reg,rfl,fun x y=>by simp [logHessian],Start.zero_bound⟩
     exact ⟨Start.zero_reg,rfl,fun x y=>by simp [logHessian],Start.zero_bound⟩
   refine ⟨fun i=> (hv i).1,fun i=> (hv i).2.1,fun i _ x y _ _=>(hv i).2.2.1 x y,?_,T,fun i=>(hv i).2.2.2,fun o=>?_⟩
   · intro s b; refine ⟨sends (sheetAction s b),fun i=> ?_⟩; unfold slate; dsimp only [comp_apply]; simp_rw [name_sends, eInfo_transport,fixed_sends]; refine ⟨trivial,trivial,fun U=>?_⟩; split; next hu =>
         cases name (Sheet n) i with
         | inl m=>
            change u * element G f (Key.perm s b m).positive U = u * element G f m.positive (pull s b U)
            have he (m:Key n) (U:Config G n): element G f m.positive U= element G f m.root (m.frame U):=h.turns ..
            rw [he, Key.oriented, he m (pull s b U)]; rfl
         | inr _=>rfl
     rfl
   let g(t:Sheet n):= if (eInfo t).site=o then p.mass (eInfo t).support (E t) else 0
   refine Padded.budget (g:=g) (fun i=>?_) (fun i=>?_) ?_
   · by_cases hh:fixed (Sheet n) i; · unfold T; rw [if_pos hh,if_pos hh]; rfl
     unfold T; simp only [hh,if_false,BudgetPoint.mass,mul_zero,ite_self]
   · unfold g; split; next h =>
         exact mul_nonneg (Real.exp_pos _|>.le) (show 0≤ E i from by unfold E; rcases i with _|_; exact hb; exact le_rfl)
     exact le_rfl
   unfold eyeG
   rw [Fintype.sum_sum_type, sum_eq_zero (s:=univ) (f:=fun i=> g (Sum.inr i)) (fun i _=> (by simp only [E,g,BudgetPoint.mass,Sum.elim_inr,mul_zero,ite_self])),add_zero]
   have he(t:Key n) (ht:t.native=o): g (.inl t)≤ Real.exp (S.supportExponent*5^4)*κ:=by
      unfold g; change ite (t.native=o) (p.mass t.skin κ) 0≤_; rw [if_pos ht]; unfold BudgetPoint.mass; apply mul_le_mul_of_nonneg_right _ hb; rw [← hS]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ S.price_pos.le; exact_mod_cast (skin_cost (b:=p) t)
   rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _ : Cell n => _)]
   rw [show _*(|u| * (_*_:ℝ))=∑ _b:Signed,∑ x:Site n,∑ _i:PlaqAxes,(if x=o then Real.exp (S.supportExponent*5^4)*κ else 0) from (by simp [κ,s]; ring)] -- fix metavars
   refine sum_le_sum fun i _=> sum_le_sum fun x _=> sum_le_sum fun b _=> ?_
   by_cases h:x=o; · rw [if_pos h]; exact he (i,x,b) h
   unfold g; change ite (x=o) _ _ ≤ _; simp [h]
end YM.WilsonStartup.IterationFour
