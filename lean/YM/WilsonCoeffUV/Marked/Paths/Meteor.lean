import YM.WilsonCoeffUV.Marked.Paths.Lift
import YM.WilsonCoeffUV.Marked.Paths.Buds
/-!
# Root aggregate Ward lift. Absolute polynomial multiplicities. No horizon dependence
other than rank and gauge for EACH width; a finite order list is priced by table.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Work.F03
variable {G:Gauge}{n:Side}{k h r t i j e:ℕ}{s A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V]

abbrev Panel (r:ℕ):= Fin r → Edge Cover
abbrev RouteP (G:Gauge)(b:Panel r):= (i:Fin r) → wordBand G (b i)
abbrev RadP (G:Gauge)(r:ℕ):= Σ b:Panel r, RouteP G b
-- measure for paths from root. Rank0 pay. use ∑ over path publication. common universal Slot declaration.
def arcs (x:Panel r):= tread Bank.terrain 0 x
lemma size_v (x:Panel r)(i:Fin r): size (x i).1≤ arcs x:= by
    have he:= leg_le Bank.terrain (stud 0 x) (0:Fin (r+1)) i.succ; change size ((x i).1-0)≤_ at he; rw [sub_zero] at he; exact he

def meteor (T:Ten V (YForest G) r)(x:RadP G r):Comet G V r:=⟨fun j=> bladeP (x.2 j), fun i=>(∏ j,glisten (x.2 j)) • T (fun j=> stone (x.1 j) (i j))⟩
def reserve (C:Comet G V r):= ∑ j,(C.sl j).length
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma ray_m (C:Comet G V r)(v:Stationary.Ink G r): (rayOne C v).magnitude=1:=by
    unfold Atom.magnitude; rw [Finset.sum_eq_single v]; simp [rayOne]; · intro i _ h; simp [rayOne,h]
    simp
omit [NormedSpace ℝ V] in
lemma ink_pos (X:Comet G V r) : 0≤ integerP X s:= Finset.sum_nonneg fun i _=> mul_nonneg (norm_nonneg _) (mul_nonneg (by rw [ray_m]; norm_num) (by positivity))
omit [NormedSpace ℝ V] in
lemma bend_in (X:Comet G V r){s t:ℝ}(h:s≤ t): integerP X s≤ integerP X t:= Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right h (by positivity))) (by rw [ray_m]; norm_num)) (norm_nonneg _))
lemma countP (x:Panel r): Fintype.card (RouteP G x)≤ (arcs x)^r:=by
    rw [Fintype.card_pi]; apply le_trans (Finset.prod_le_prod (fun i _=> Nat.zero_le _) (g:=fun _=> arcs x) (fun i _=>?_)) (by simp)
    rw [show Fintype.card (wordBand G (x i)) = (turnPlan G (x i)).length from Fintype.card_fin _]; exact (turn_bounds G (x i)).1.trans (size_v x i)
lemma meteor_fee (T:Ten V (YForest G) r)(p:RadP G r): reserve (meteor T p) ≤ 8*r*(1+arcs p.1):=by
    let cuspCap:= arcs p.1+1
    calc
     _≤∑ _ : Fin r, (4*cuspCap + 4):= by
       apply Finset.sum_le_sum; intro i _; apply le_trans (glower (p.2 i)); unfold cusp cuspCap; gcongr; exact size_v p.1 i
     _ ≤ _:=by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; apply le_trans _ (show 8*r*(1+_)=8*r*(1+arcs p.1) from rfl).le; unfold cuspCap; nlinarith only [Nat.zero_le r,Nat.zero_le (r*arcs p.1)]
lemma meteor_m (T:Ten V (YForest G) r)(p:RadP G r)(x:Stationary.Ink G r): ‖(meteor T p).wage x‖ = ‖T (fun i=>stone (p.1 i) (x i))‖:=by unfold meteor; dsimp only; simp only [norm_smul, norm_prod, glow, Finset.prod_const_one,one_mul]
-- ash names reorder absolute moments

def terrace (G:Gauge) (r:ℕ): Panel r × Stationary.Ink G r ≃ (Fin r→ YForest G) where
    toFun x i:= stone (x.1 i) (x.2 i)
    invFun x:= (feather ∘ x, fun i=> (x i).2.2)
    left_inv x:= Prod.ext (funext fun i=>feather_at (x.1 i) _) rfl
    right_inv x:= funext fun i=> by
       obtain ⟨u,j,z⟩:= every_stone (x i); change stone (feather (x i)) (x i).2.2= x i; rw [← z,feather_at]; rfl

def humidity (s:ℝ)(r:ℕ):ℝ := s/(16*(r+1:ℕ))
def christmas (G:Gauge)(s:ℝ)(r:ℕ):ℝ := Real.exp (s/2)*(ceilPoly r ((s-s/2)/2)* tiePay (Hooks G) r ((s-s/2)/2))
lemma mist (h:0<s)(r:ℕ): 0<humidity s r:=div_pos h (by positivity)
lemma floatPrice {T:Ten V (YForest G) r}(p:Twig 0 s A T)(h:0<s): SumBudget (fun j=>integerP (meteor T j) (humidity s r)) (christmas G s r*A):=by
    let L:=terrace G r; let U (x:Fin r→YForest G):ℝ:= (1+(port_d 0 x):ℝ)^r*Real.exp (s/2*(port_d 0 x))*‖T x‖
    let E:= Real.exp (s/2); have he: 0≤ E:= (Real.exp_pos _).le; let Z(x:Panel r× Stationary.Ink G r):=E*U (L x)
    have hx: SumBudget U ((A*ceilPoly r ((s-s/2)/2))*tiePay (Hooks G) r ((s-s/2)/2)):= shrub V T p (half_lt_self h) r
    have hp : SumBudget Z (christmas G s r*A):=by
       have hh := cap_scale hx he; unfold christmas; refine ⟨fun i=>hh.1 (L i),L.summable_iff.mpr hh.2.1,?_⟩; unfold Z; rw [L.tsum_eq (fun i=> E*U i)]; exact hh.2.2.trans_eq (by unfold E; ring)
    let B(x:Panel r):= ∑ a:Stationary.Ink G r,Z (x,a); let F (x:RadP G r):=integerP (meteor T x) (humidity s r)
    have hz:B= (fun i=>∑' j,Z (i,j)):= by funext i; rw [tsum_fintype]
    have H : SumBudget B (christmas G s r*A):= by
       rw [hz]; refine ⟨fun i=>tsum_nonneg fun j=> hp.1 _, hp.2.1.prod, ?_⟩; rw [←hp.2.1.tsum_prod]; exact hp.2.2
    have hv (x): ∑' b:RouteP G x,F ⟨x,b⟩ ≤ B x:=by
       let d:ℝ:= arcs x
       let S (a:Stationary.Ink G r):=‖T (L (x,a))‖
       have hb a:0≤ S a:= norm_nonneg _; have ht:0≤d:=by unfold d; positivity
       rw [tsum_fintype]; change ∑ b, ∑ a,_≤_
       rw [Finset.sum_comm]; apply Finset.sum_le_sum; intro a _; let C:= S a*Real.exp ((s/2)*(1+d))
       have hC:0≤ C:=mul_nonneg (hb _) (by positivity)
       refine (Finset.sum_le_sum (g:=fun _=> C) (fun b _=>?_)).trans (le_trans (le_of_eq ?_ : ∑ _ :RouteP G x,C ≤ Fintype.card (RouteP G x)*C) ?_)
       · let A:=meteor T ⟨x,b⟩; unfold Atom.budget; rw [meteor_m, ray_m,one_mul]; apply mul_le_mul_of_nonneg_left _ (hb _); apply Real.exp_le_exp.mpr; change humidity s r*reserve A ≤ _
         apply le_trans (mul_le_mul_of_nonneg_left (show (reserve A:ℝ) ≤ (((8*r*(1+arcs x)):ℕ):ℝ) from by exact_mod_cast meteor_fee T ⟨x,b⟩) (mist h r).le); unfold d humidity; push_cast
         rw [div_mul_eq_mul_div]; apply (div_le_iff₀ (by positivity)).mpr; nlinarith [mul_nonneg h.le ht]
       · simp
       have ha: (Fintype.card (RouteP G x):ℝ) ≤ (1 + d)^r:= by apply le_trans (show (Fintype.card (RouteP G x):ℝ)≤ d^r from by unfold d; exact_mod_cast (countP (G:=G) x)); gcongr; simp
       apply (mul_le_mul_of_nonneg_right ha hC).trans_eq; unfold C S d Z E U; rw [show port_d 0 (L (x,a))= arcs x from rfl, show s/2*(1+_)=s/2+s/2*arcs x from by ring, Real.exp_add]; ring
    have h' x:0≤ F x:=ink_pos _
    have hh:Summable F:= (summable_sigma_of_nonneg h').mpr ⟨fun i=> summable_of_hasFiniteSupport (Set.toFinite _),H.2.1.of_nonneg_of_le (fun _=> tsum_nonneg fun i=> h' _) hv⟩
    exact ⟨fun i=>h' i,hh,by change tsum F≤ _; rw [hh.tsum_sigma]; exact (Summable.tsum_le_tsum hv hh.sigma H.2.1).trans H.2.2⟩
end YM.WilsonCoeffUV.Mer.Rolls
