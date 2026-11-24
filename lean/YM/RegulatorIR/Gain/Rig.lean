import YM.RegulatorIR.Gain.Desk

/-!
# Curves-bill

pre/post distinct; sites to edges shift costs ≤ 2^u per shift in output-site
distance. Roll budgets without normal group dimension dependence except pet
finite group constants. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{I J X Y Z:Type}{f c:Side}{P l u:ℝ}{m b t:ℕ}
-- cemetery cap
section Legs
variable (S : I→ Prop) (U:Layer I J)(A:Tariff Z)(x:I→Z)(y:J→Z)
lemma zoom {v:ℝ≥0∞}(h:Layer.row U A x y v) : Layer.row (Function.swap (leggy U)) A (Sum.elim x y) (Sum.elim x y) v:=by
 intro i; cases i
 next i=>
    change (∑'z:I⊕J, ‖Function.swap (leggy U) (Sum.inl i) z‖ₑ*_) ≤ _
    rw [← (Sum.inr_injective (α:=I) (β:=J)).tsum_eq]
    exact h i
    rintro (j|j) he
    · exfalso; apply he; change ‖(0:ℝ)‖ₑ*_=0;simp
    exact ⟨j,rfl⟩
 next j=> rw [show Function.swap (leggy U) (Sum.inr j)=0 from funext fun z=>by cases z <;> rfl, quota_zero]; exact bot_le

lemma lineCost {X:Type} {T:Tariff X}{y:I→X}{x z:X}(F:I→ℝ): quota F (fun i=>T.road x (y i))≤ T.road x z*quota F fun i=>T.road z (y i):=by
 unfold quota; rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum; intro a; exact (mul_le_mul_right (T.tri x z (y a)) _).trans_eq (mul_left_comm ..)

end Legs

variable {A: Deck P (Foot G) (Book G f)} {B: Deck P (Foot G) (Book G c)} (D: GridStep A B) (J₀:Layer (Foot G) (Foot G))(V:Bride G)
variable (hl:0<l)(hu:l≤u)
local notation "C0" => Tariff.native u (hl.trans_le hu) b -- linter local vars
variable {v w:ℝ≥0∞}
-- Native costs compare roof. width changes with root coordinate bounded uniformly ≤1 output distance. no terminal.

def localL (l:ℝ)(x:Foot G): Room:= Geometry.seat l x.1
include hl
lemma rate₀ (i:Axis) : ‖slide l (step i)‖=l:= by
 rw [show slide l (step i)=l • (Lattice.step i:Room) from ?_,norm_smul,Real.norm_of_nonneg hl.le,Lattice.step,Pi.norm_single]; simp
 ext1 j; by_cases h:j=i<;> simp [h]
lemma rate₁ (x:Foot G) : dist (localL l x) (slide l x.1.1)=l/2:=by
 unfold localL seat glint; rw [dist_eq_norm_sub,add_sub_cancel_left,norm_smul,rate₀ hl]; norm_num;ring
lemma rate₂ (x: Foot G): dist (localL l x) (slide l (x.1.1+step x.1.2))=l/2:=by
 unfold localL seat glint; rw [dist_eq_norm_sub,map_add,add_sub_add_left_eq_sub];
 let y := slide l (step x.1.2)
 rw [show (1/2:ℝ) • slide l (step x.1.2)-_= -((1/2:ℝ) • y) by unfold y; module,norm_neg, norm_smul, show ‖y‖= _ from rate₀ hl x.1.2]; norm_num;ring

include hu
lemma sector_move : Tariff.amount u b (l/2) ≤ 2^b:=by
 have h:0<u:= hl.trans_le hu; apply pow_le_pow_left'; apply le_trans _ (show (2:ℝ≥0∞)=2 from rfl).le; rw [← ENNReal.ofReal_ofNat (n:=2)] -- name
 apply ENNReal.ofReal_le_ofReal; have he : l/2/u ≤1:= (div_le_one h).mpr (by linarith);linarith

variable (y:Foot G→Room)
-- scope K cover
lemma stride (h:row J₀ C0 (localL l) y v)(he:row V C0 (pointS l) y w) (x:Foot G) (j: Mood G):quota (tubeL J₀ V x.1 j) (fun i=> (C0).road (localL l x) (y i)) ≤ v+ (2:ℝ≥0∞)^b*w:=by
 rcases j with ⟨i,p⟩; fin_cases i
 · exact (h (x.1,p)).trans (le_add_right le_rfl)
 · refine le_trans (lineCost (z:=pointS l ((x.1.1,p):Point G)) (V (x.1.1,p))) ?_
   rw [show (C0).road (localL l x) (pointS l (x.1.1,p))= _ from congr_arg (Tariff.amount u b) (rate₁ hl x)]
   exact (mul_le_mul' (sector_move hl hu) (he (x.1.1,p))).trans (le_add_left le_rfl)
 refine le_trans (lineCost (z:=pointS l ((x.1.1+step x.1.2,p):Point G)) (V (x.1.1+step x.1.2,p))) ?_
 rw [show (C0).road (localL l x) (pointS (G:=G) l (x.1.1+Lattice.step x.1.2,p))= _ from congr_arg (Tariff.amount u b) (rate₂ hl x)]; exact (mul_le_mul' (sector_move hl hu) (he _)).trans (le_add_left le_rfl)

variable (hP:0<P)
local notation "C1" => Tariff.onFold P hP u (hl.trans_le hu) b
variable (h: Even f.val)(hz:l*f.val=P) (x:Book G f)
local notation "R" => Carto G l P h hz

include hP hz
omit hl hu in
lemma reach (v a:Cover)(he : wrap f v =wrap f a)(x): distance P x (Motion.slide l v)= distance P x (Motion.slide l a):=by
 obtain ⟨w,hc⟩:= gramE he;rw [hc, roam_x, hz, distance_deck hP]
lemma strideO (H:row J₀ C0 (localL l) B.pos v)(he:row V C0 (pointS l) B.pos w) (j:Mood G): quota (tubeO (wrapL R B J₀) (scene V B) x.1 j) (fun i=> (C1).road ((R).atO x) (B.atO i)) ≤ v +(2:ℝ≥0∞)^b*w:=by
 have hp:= row_cost R B J₀ hP (hl.trans_le hu) b H; have hF:= hike b (hl.trans_le hu) hP (f:=f) V B he
 rcases x with ⟨i,v⟩
 let x : Book G f:=(i,v); let u0:=(R).place x
 rcases j with ⟨t,q⟩;fin_cases t
 · exact (hp (i,q)).trans (le_add_right le_rfl)
 · apply le_trans (lineCost (z:=pointO l ((i.val.1,q):OPoint G f)) (scene V B (i.val.1,q))); apply le_trans _ (le_add_left le_rfl)
   apply mul_le_mul' _ (hF _)
   apply le_trans _ (sector_move hl hu); apply Tariff.amount_mono (hl.trans_le hu) b
   exact (distance_le hP _ _ (.across 0)).trans_eq (by rw [neutral_loc]; exact rate₁ hl u0)
 let z:OPoint G f:=(i.val.1+step i.val.2,q)
 apply le_trans (lineCost (z:=pointO l z) (scene V B z)); apply le_trans _ (le_add_left le_rfl);apply mul_le_mul' _ (hF _); apply le_trans _ (sector_move hl hu); apply Tariff.amount_mono (hl.trans_le hu) b
 change distance _ _ (slide l (Lattice.lift z.1))≤ _
 have hx : wrap f (Lattice.lift z.1)=wrap f (u0.1.1+step u0.1.2):=by rw [wrap_lift,map_add,wrap_step];change _=wrap f (Lattice.lift i.val.1)+_;rw [wrap_lift];rfl
 rw [reach hP hz _ _ hx]; exact (distance_le hP _ _ (.across 0)).trans_eq (by rw [neutral_loc];exact rate₂ hl u0)

-- global mark sum authority

omit hl hu hP hz
def hatchV (G:Gauge)(i:ℕ): ℝ≥0∞:= ∑ j:G.ColorIndex, quota (pet G j i) 1
lemma hatch_fin (G:Gauge)(i:ℕ) : hatchV G i≠⊤:=by unfold hatchV; apply ENNReal.sum_ne_top.mpr; intro k _; rw [quota_base,tsum_fintype]; exact ENNReal.sum_ne_top.mpr (fun _ _=> enorm_ne_top)
lemma hatch_ge (G:Gauge)(j:G.ColorIndex)(i) : quota (pet G j i) 1≤ hatchV G i:= Finset.single_le_sum (fun v _=> (show 0 ≤ quota (pet G v i) 1 from bot_le)) (Finset.mem_univ _)
end YM.RegulatorIR.Gain
