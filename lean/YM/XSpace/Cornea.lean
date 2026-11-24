import YM.XSpace.Passes
/-!
# Seats cost codification for distinct and masked three cubic attachments
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gland
open Function Set Filter Trace Relief Tide Sail Lattice Chart2 Chiral Octave Graph3 Mu MvPolynomial Asymptotics
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{G:Gauge}{V:ι→Cover→Prop} {i j k:ℕ}
local notation "W" => G.ColorIndex
abbrev NoCut : ι→ Cover→Prop:= fun _ _=>True
def board (V:ι→Cover→Prop)(L:Filter ι)(a:ι→ℝ)(x y z:ι→Cover):Prop:=∀ (i j k:ℕ),i≤1→ j≤1→ k≤1 → Dance V L a (5+i+j+k) (fun t=>Form (x t) (y t) (z t) (rate (3+i)) (rate (3+j)) (rate (3+k)))
variable (s:Stage L a)
include s in
lemma diastole (h:Ensemble L a x y z): board NoCut L a x y z:=by intro i j k hi hj hk; rw [show 5+i+j+k=3+i+(3+j)+(3+k)-4 by omega]; exact jamb s h (by omega) (by omega) (by omega) (by omega) (by omega)
include s in
lemma systole (h: Beats V L a x): board V L a x x x:=by
  intro i j k hi hj hk; unfold Form; simp_rw [moon_mul]; rw [show 5+i+j+k= 3+i+(3+j)+(3+k)-4 by omega]; exact on_pitch s h (by omega)
include s in
lemma surface (h:Beats V L a z)(hm:distFee L a (fun i=>x i-y i)): board V L a x y z:= by
  intro i j k hi hj hk; rw [show 5+i+j+k=3+i+(3+j)+(3+k)-4 by omega]; exact versatile s (by omega) (by omega) (by omega) (by omega) hm h
lemma reflected (h:board V L a x y z): board V L a y x z:=by intro i j k hi hj hk; simp_rw [form_flip (rate (3+j))]; rw [add_right_comm 5 i j]; exact h j i k hj hi hk
lemma wheeled (h:board V L a x y z): board V L a y z x:=by intro i j k hi hj hk; simp_rw [form_turn (rate (3+k))]; rw [show 5+i+j+k=5+k+i+j by omega]; exact h k i j hk hi hj
abbrev Marked (c:Shade.Cut)(a:ι→ℝ)(x:ι→Cover):= fun i w=> Season.strip c (a i) (w-x i)≠0
include s in
lemma vent (c:Shade.Cut)(x:ι→Cover): Beats (Marked c a x) L a x:=by
  refine ⟨c.rIn/2,half_pos c.rIn_pos, s.good.mono fun i hi w hh=>?_⟩; have ht:= Season.exc c _ _ (fun H=> hh (by unfold Season.strip; rw [H,sub_self])); unfold pad Drama.area; linarith [(Shade.size_actual hi (w-x i)).2]
-- rate on the individual contractions unnormalized
abbrev collation (p q:Line G)(x y:Cover):= col (displace x p) (displace y q)
lemma stampede (p q: Line G)(x y:Cover): collation p q x y= collation p q (x-y) 0:=by
  unfold collation col; rw [originate]; congr 1; apply Eq.symm; rw [← meter_serves _ q y, displacement,add_comm y,sub_add_cancel]
lemma toll_booth (P Q:Line G)(Hp:P∈cane i G)(Hq:Q∈cane j G): ∃ C:ℝ,0≤C∧∀ x y:Cover, ‖collation P Q x y‖≤ C*rate (2+i+j) (x-y):=by
  obtain ⟨C,hC,H⟩:= line_receipt Hp (advertised _ Q Hq); exact ⟨C,hC,fun x y=>by rw [stampede P Q x y,collation,col,originate, Complex.norm_real, Nat.add_right_comm 2]; exact H _⟩
include s in
lemma fare_stake (P Q:Line G)(Hp:P∈cane i G)(Hq:Q∈cane j G)(hv:distFee L a (fun i=>x i-y i)): funds L a (2+i+j) (fun t=>collation P Q (x t) (y t)):=by
  obtain ⟨C,hC,H⟩:= toll_booth P Q Hp Hq; refine IsBigO.trans ?_ (stage_price s hv _); exact IsBigO.of_bound C (Eventually.of_forall fun i=> by rw [Real.norm_of_nonneg (carry_pos ..).le]; exact H _ _)
-- the ribbon of three lines anchored (unscaled, all over projected heights)
variable (x y z:Cover)(P Q R:Line G)
def sign (A B C:Line G)(w: Cover): ℂ:= collation A P w x * collation B Q w y * collation C R w z
variable {x y z P Q R} {A B C:Line G} (hp:P∈cane 1 G)(hq:Q∈cane 1 G)(hr:R∈cane 1 G)(ha:A∈ cane i G)(hb:B∈cane j G)(hc:C∈cane k G)
include hp hq hr ha hb hc in
lemma locus : ∃ C':ℝ,0≤C'∧∀ x y z w:Cover, ‖sign x y z P Q R A B C w‖ ≤ C' * ‖Form x y z (rate (3+i)) (rate (3+j)) (rate (3+k)) w‖:=by
  obtain ⟨p,hp,H⟩:= toll_booth _ _ ha hp; obtain ⟨q,hq,K⟩:=toll_booth _ _ hb hq; obtain ⟨r,hr,J⟩:= toll_booth _ _ hc hr; refine ⟨p*q*r,by positivity,fun x y z w=>?_⟩; unfold sign Form; simp_rw [add_right_comm 2 _ 1] at H K J; simp_rw [norm_mul]; simp_rw [Real.norm_of_nonneg (Octave.sound ..).le]; exact (mul_le_mul (mul_le_mul (H w x) (K w y) (norm_nonneg _) (mul_nonneg hp (Octave.sound ..).le)) (J w z) (norm_nonneg _) (mul_nonneg (mul_nonneg hp (Octave.sound ..).le) (mul_nonneg hq (Octave.sound ..).le))).trans_eq (by ring)
lemma sign_fin (x y z:Cover) (P Q R:Line G)(hp:P∈ cane 1 G)(hq:Q∈cane 1 G)(hr:R∈cane 1 G) (A B C:Line G): Summable (sign x y z P Q R A B C):=by
  obtain ⟨p,ht,H⟩:= locus hp hq hr (Trace.tariff A) (Trace.tariff B) (Trace.tariff C); exact Summable.of_norm_bounded (((chord_free (i:=3) (j:=3) (by norm_num) 3).norm).mul_left p) (H x y z)
variable {x y z:ι→Cover}
include hp hq hr ha hb hc in
lemma sign_toll (H:board V L a x y z)(h:i≤1)(P':j≤1)(h':k≤1): Dance V L a (5+i+j+k) (fun i=> sign (x i) (y i) (z i) P Q R A B C):=by
  obtain ⟨p,hp,E⟩:= locus hp hq hr ha hb hc; exact tango (H i j k h P' h') hp (Eventually.of_forall fun i u _=> E (x i) (y i) (z i) u)
end YM.XSpace.Gland
