import YM.Frontier6.Bouquet.Carnival.Croquet

/-! Extend the Terrain by the request for a shell on i; its radius counts in
 costs and comparison penalties independently of the regulator. Exactly **one**
 common projection memory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (K:Final C F S) {P Q:Ensemble}{d:Slot →ℕ}(i:P) (M:Pod→ℝ)
variable (p:Part d i)
def slope : ℕ:= match p with
 | none=> i.val.horizon d
 | some w=> w.val
variable (A: Aura P)
def ruffle (A:Aura P)(r:ℝ): Aura P:= ⟨A.center,update A.foot i ((A.foot i)∩closedBall (A.center i) (2*r))⟩
lemma ruffles {j:P}(h:j≠i)(r:ℝ): (ruffle i A r).foot j=A.foot j:= update_of_ne h _ _
lemma ruffled (r:ℝ): (ruffle i A r).foot i=A.foot i∩closedBall (A.center i) (2*r):= update_self ..
lemma ruff_shrunk (r:ℝ): (ruffle i A r).foot≤A.foot:= by intro j; by_cases h:j=i; subst j; rw [ruffled]; exact inter_subset_left; rw [ruffles i A h r]
lemma ruff_cozy {M:Pod→ℝ}(he:A.Cozy M){r:ℝ}(hr:0<r): (ruffle i A r).Cozy M:= by
    constructor
    · intro j; change A.center j∈_; by_cases h:j=i; subst j; rw [ruffled]; exact ⟨he.around i, mem_closedBall_self (mul_pos two_pos hr).le⟩; rw [ruffles i A h r]; exact he.around j
    · intro j; by_cases h:j=i; subst j; rw [ruffled]; exact (he.solid i).inter (convex_closedBall ..); rw [ruffles i A h]; exact he.solid j
    exact fun j x hx=> he.prices j x (ruff_shrunk i A _ j hx)
variable (R: Air (S:=S) P I L Y) (B: ℝ)
-- parameters without s avoids changing local-radius trajectory if program memory changes
structure Swing where
   here : I
   radius : ℝ
   pos : 0<radius
   edge : radius≤1
   back : p=none→ radius ≤ 2*B*(R.lengths here i)
variable (z:Swing i p R B)
local infix:40 "∥∥" => Min.min

def roads : Audit.Ribbon (Swing i p R B) (Option L) where
    floor z:= R.route.floor z.here ∥∥ z.radius
    length z v:= match v with | none=> z.radius | some x=> R.route.length z.here x
    covered z v:= by cases v; exact ⟨min_le_right ..,z.edge⟩; rename_i x; exact ⟨(min_le_left ..).trans (R.route.covered ..|>.1),R.route.covered z.here x|>.2⟩
    ground z:= ⟨lt_min (R.route.footing _) z.pos,(min_le_right ..).trans z.edge⟩
def landscape : Air (S:=S) P (Swing i p R B) (Option L) Y where
    route := roads i p R B
    role := fun j=> if j=i then none else some (R.role j)
    region z := ruffle i (shift i p (R.region z.here) M) z.radius
    sky z:= moves K i (R.sky z.here) p (R.region z.here).center
    account z:= R.account z.here* (z.radius/(R.lengths z.here i))^(slope i p)

lemma techno : (landscape K i M p R B).lengths z= update (R.lengths z.here) i z.radius:= by
  ext1 j; unfold Air.lengths landscape; dsimp only; by_cases h:j=i; subst j; rw [if_pos rfl,update_self]; rfl; rw [if_neg h,update_of_ne h]; rfl
set_option quotPrecheck false
local notation "Φ"=> landscape K i M p R B
lemma land_center : ((Φ).region z).center=(R.region z.here).center:= shifts ..
lemma land_welkin (he:Dais K d P M)(hp:R.Welkin M): (Φ).Welkin M:= ⟨fun _=> ruff_cozy i _ (shift_cozy i _ (hp.safe _)) (Swing.pos _),fun _=> Gentle.lesser (unflag i p he (hp.safe _) (hp.smooth _)) (ruff_shrunk i _ _),fun x=> mul_pos (hp.pos _) (pow_pos (div_pos x.pos (R.length_pos ..)) _)⟩ -- variables reordering

-- parent aggregation for one variable, in Hosts station
section
variable (f : J→ Swing i p R B)(T:Fareway J)[T.via.NeBot] {a b u:ℝ}{L':Finset ℝ}{v:Art S J}
local notation "α"=>fun j:J=>R.lengths (f j).here i
local notation "β"=>fun j:J=>(f j).radius
local notation "y"=>fun j:J=>(f j).here
local notation "c"=>fun j:J=>(R.region (f j).here).center i
lemma slides (he:Dais K d P M)(hp:R.Welkin M)(ht:T.Mint β (-b))(hr:T.Mint α (-a))(h: b∈ L')(hB:0<B)(hz:Pen K T L' b ((Φ).foci f i) v u):
    Pen K T L' a (R.foci y i) (fun j=> movedBy K i p (c j) (v j)) (u-(slope i p:ℝ)*(b-a)):=by
    let A:= (Φ).foci f i; have hc:Local T A c b:=by
       intro z hz; filter_upwards [((T.minted_c 2 two_pos).mul ht).cheaper (T.minted (-z)) (by linarith)] with j hj z hz; refine le_trans ?_ hj.le; change z∈(ruffle i (shift i p (R.region (y j)) M) (f j).radius).foot i at hz; rw [ruffled,shifts] at hz; exact (dist_eq_norm z (c j)).symm.trans_le (mem_closedBall.mp hz.2) -- z duplicate hazard
    have hU:= land_welkin K i M p R B he hp
    have ht':Contains T A c:=Eventually.of_forall fun j=> by dsimp only; rw [←land_center K i M p R B (f j)]; exact (hU.safe _).around _
    have hv(w:ℕ)(hw:w≤ i.val.horizon d): Forest.Centered T A c K w:= ⟨M i.val,(he.safe _ (stage_in i.property)).down K hw le_rfl,he.pos _ (stage_in i.property), Eventually.of_forall fun j z hz=> (congr_arg (fun x:Seats P=> ‖z-x i‖) (land_center K i M p R B (f j))).symm.trans_le ((hU.safe _).prices i _ hz)⟩
    cases p -- dependent stuff; generalized f!
    · have hv': a≤ b:=by
        by_contra hj; obtain ⟨j,hj⟩:= (((T.minted_c _ (mul_pos zero_lt_two hB)).mul hr).cheaper ht (by linarith)).exists; exact hj.not_ge ((f j).back rfl)
      have hh:Extends T (R.foci (fun j=>(f j).here) i) ((landscape K i M none R B).foci f i):= Eventually.of_forall fun j=> ruff_shrunk i (R.region (f j).here) (f j).radius i -- specify apply
      dsimp only [slope,movedBy]; generalize hk:i.val.horizon d=k; cases k with
      | zero=> simp only [Nat.cast_zero, zero_mul,sub_zero, advance_value,Fintype.sum_empty]; exact (hz.feed h hv' hc ht').weaker hh
      | succ k=>
        have he:= hv k (by omega); simp only [Nat.cast_add_one]; exact ((hz.refuse h hv' hc ht' k he).cf ((lights K k he hz.intact).mono fun j hj=> (advance_high K _ hj).symm)).weaker hh
    rename_i w; dsimp only [slope,movedBy]; have he':= hv _ w.isLt.le; exact (hz.pass h hc (Eventually.of_forall fun j=> (hp.safe _).around i) w he').cf ((lights K _ he' hz.intact).mono fun j hj=> (stage_part K _ hj).symm)
end
end YM.Frontier6.Bouquet.Atelier
