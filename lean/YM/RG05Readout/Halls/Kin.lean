import YM.RG05Readout.Halls.Forks
/-!
# Spacing from charged profile geometry in physical WM units

Probes only need Cartesian separation of actual body supports in their *same*
roots. Native header ensures no testing on foreign cells despite wrap. Price
traces at the top.Occ constraints: across distinct copies need peg at initial
capture, then mere spreading as in Genesis. Labels projected from color
position, turned translations applied to center itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g:ℕ}
set_option quotPrecheck false
local notation "S'"=> C.S
local notation "Πξ"=> C.S.toDepth
local notation "ψ"=> C.path.levels.clock
local notation "K"=> C.path.levels.clock.op
local notation "α"=> C.S.a
local notation "G!"=> C.S.gridPoint
local notation "λ!"=> C.side
local notation "ω"=> Lattice.wrap
local notation "Z!"=>C.path.levels.budget
local notation "χ"=> (C.S.radius p)
local notation "X!"=> C.side n p
section geometry
lemma grid_sub (a b:Cover): G! n (a-b)=G! n a-G! n b:=eq_sub_of_add_eq (Eq.trans (Work.B16.grid_add (C:=C) ..).symm (congr_arg _ (sub_add_cancel a b)))
lemma within_phys (w:Cover) (hp:‖G! n w‖ < χ): lift (Lattice.wrap X! w)=w:=by
    apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro i
    let A:= α n; let B:ℕ:=(X!).val; have hg:0<A:= (S').a_pos n; have hx : |A*(w i:ℝ)| < χ:=lt_of_le_of_lt (PiLp.norm_apply_le ((S').gridPoint n w) i) hp
    have he:2*χ=A*B:=by unfold Schedule.radius;rw [← (S').span_side n p]; ring
    have hy:=abs_lt.mp hx; have hL:-(B:ℝ)<2*w i:=by refine lt_of_mul_lt_mul_left ?_ hg.le; linarith only [he,hy.1]
    have hk : (2:ℝ)*w i < B:=by refine lt_of_mul_lt_mul_left ?_ hg.le; linarith only [he,hy.2]
    exact ⟨by exact_mod_cast hL, le_of_lt (by exact_mod_cast hk : 2*w i < B)⟩
lemma phys_space (a b:Cover)(hp:‖G! n a-G! n b‖ < χ) : ‖G! n a-G! n b‖ ≤ 2*(α n)*separation (ω X! a) (ω X! b):=by
    let V:= (ω X! a-ω X! b)
    rw [← grid_sub] at hp ⊢; have he: lift V=a-b:=by unfold V;rw [← map_sub];exact within_phys (p:=p) _ hp
    exact (le_trans (le_of_eq (by change ‖G! n _‖= ‖G! n (lift V)‖;rw [he])) (le_trans (Ribbons.normC C n p V).2 (by simp only [separation,sub_zero];exact le_rfl)))

lemma box_t (z:E4)(hz:z∈Native.box):‖(α n) • z‖≤ α n:=by rw [norm_smul,Real.norm_of_nonneg ((S').a_pos n).le]; exact mul_le_of_le_one_right ((S').a_pos n).le (Pert.Cellular.cells_bd hz)

variable {R a:ℝ}
lemma pair_verified (v u w z:Cover)(hh:n≤ m) (x y x' y':E4)(hv:x∈Native.box)(hu:y∈Native.box)(hw:x'∈Native.box)(hz:y'∈Native.box)
   (ht:G! n v+(α n) • x=G! m w+(α m) • x')(hs:G! n u+(α n) • y=G! m z+(α m) • y')
   (hp: ‖G! n v‖≤ R*(α n))(h'p: ‖G! n u‖≤ R*(α n))(hX: 2*(R+2)*(α n) < χ) (hy:a ≤ ‖(G! n v+(α n) • x)-(G! n u+(α n) • y)‖) (he:2*(α m)*(1+((Z! m).B:ℝ)^2)<a) :
    (Z! m).B^2+1 ≤ separation (ω (λ! m p) w) (ω (λ! m p) z):=by
    let J:= G! m w; let V:= G! m z; let b:=α m; let X:= J+b • x'; let Y:= V+b • y'; have hQ : b≤ α n:= (S').strictAnti.antitone hh; have hB:‖X-Y‖ ≥ a:=by rw [ht,hs] at hy; exact hy
    have h₁:‖X‖≤ R* (α n)+α n:=by apply (ht ▸ (norm_add_le ..)).trans; exact add_le_add hp (box_t _ hv)
    have h₂:‖Y‖≤ R* (α n)+α n:=by unfold Y V b; rw [← hs]; exact (norm_add_le ..).trans (add_le_add h'p (box_t _ hu))
    have h₃:‖J-X‖≤ b:=by rw [norm_sub_rev]; unfold X; rw [add_sub_cancel_left]; exact box_t _ hw
    have h₄:‖V-Y‖≤ b:=by rw [norm_sub_rev]; unfold Y; rw [add_sub_cancel_left]; exact box_t _ hz
    have hp' : ‖J-V‖ < χ:=by
       have hV' : J-V = (J-X)+(X-Y)+(Y-V):=by abel
       rw [norm_sub_rev] at h₄; rw [hV']; refine lt_of_le_of_lt ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h₃ ((norm_sub_le ..).trans (add_le_add h₁ h₂)))) h₄)) ?_; linarith only [hX,hQ]
    have hyv:= phys_space w z (C:=C) (n:=m) hp'; change ‖J-V‖ ≤ _ at hyv
    let s:= separation (ω (λ! m p) w) (ω (λ! m p) z)
    rw [norm_sub_rev] at h₃; rw [show X-Y= (X-J)+(J-V)+(V-Y) from by abel] at hB; have hy' := (hB.trans ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h₃ hyv)) h₄)))
    have hh: ((Z! m).B:ℝ)^2 < s:=by
       have h:0<b:= (S').a_pos _
       have h' : 2*b*((Z! m).B:ℝ)^2 < 2*b*(s:ℝ):=by linarith only [he.trans_le hy']
       exact lt_of_mul_lt_mul_left h' (by positivity)
    change (Z! m).B^2+1≤ s; exact_mod_cast (show (Z! m).B^2<s from (by exact_mod_cast hh)) -- edit
end geometry
section spacing
variable (c:J→Site (C.side n p)) (E:J→Motion)(v:V→ Cover)(s:V→ℕ)(W:V→Body)(F:J→Body)(Y:J→I)
local notation "y"=> (fun j:V=>Lattice.wrap (C.side n p) (v j))
local notation "U!" => Unit × Recipe J V
local notation "o"=> roads c E y
local notation "l!"=> side_E E (V:=V)
local notation "V!"=> ManyStem C (roads c E y)
local notation "T₀"=> (Mine.tree (roads c E y) (side_E E (V:=V)))
local notation "Z'"=> (T₀).supportX
local notation "s₁"=> toss s d (J:=J)
local notation "H!"=> coats c E y W F
local notation "Q!"=> partialGroup Unit (basin J V)
-- access marker even-index data.Available ticket.
def carton {V:Type} (C:Family G)(n:ℕ)(v:V→ Cover)(W:V→Body)(r:ℝ) := ∀ (i j:V), i ≠ j → ∀ a∈ Native.box∩ tsupport (W i).val,∀ b∈Native.box∩ tsupport (W j).val, r≤‖(C.S.gridPoint n (v i)+(C.S.a n) • a)-(C.S.gridPoint n (v j)+(C.S.a n) • b)‖
omit [DecidableEq V] [Fintype V] [Fintype J] [DecidableEq J] in
lemma reached (t:ℕ)(hp:∀ i:V,separation (y i) 0 ≤ t) (i:U!): separation (o i) (c i.snd.fst) ≤ t :=by
    rcases i with ⟨_,k,((_|i)|⟨⟩)⟩
    · change separation (c k) _ ≤ _; simp
    · change separation (affine (E k).1 _ _) (c k) ≤ t; unfold affine separation; rw [add_sub_cancel_right,pdist_invariant]; simpa [separation] using hp i
    change separation (c k) (c k) ≤ t; rw [separation_self]; exact Nat.zero_le _
omit [DecidableEq V] [Fintype V] [DecidableEq J] [Fintype J] in
lemma wreath (t:ℕ)(hp:∀ i:V,separation (y i) 0 ≤ t) (hv:t≤1024*((Z! n).B)^2) (i:U!): coverNumber (Z! n).B ({(o ∘ (Q!).twig) ((Q!).bunch i),o i}:Support X!) ≤ Ribbons.peepers C.path.levels n:=by
    have he :(o ∘ (Q!).twig) ((Q!).bunch i)= c i.2.fst:=by rcases i with ⟨_,k,((_|i)|⟨⟩)⟩<;> rfl
    rw [he]; let B:=(Z! n).B; let A:=1024*B; let x:=c i.2.fst; have hh := Corona.tile x A B (Z! n|>.B_pos)
    exact (Corona.cover_mono (show ({x,(o) i}:Support X!) ⊆ halo (A*B) {x} from by
       intro y' h; rcases Finset.mem_insert.mp h with h|h; · rw [h]; exact halo_spec.mpr ⟨_,mem_singleton_self _,by simp⟩
       rw [Finset.mem_singleton.mp h]; refine halo_spec.mpr ⟨_,Finset.mem_singleton_self _,?_⟩; rw [separation_comm]; exact (reached c E v t hp i).trans (hv.trans_eq (by unfold A B; ring))) B).trans (by simpa only [Ribbons.peepers,two_mul] using hh)
-- area payments
omit [DecidableEq J] in
lemma lot (ht:Occupancy c 1): Occupancy (roads c E y) (Fintype.card (Color V × Motion)):=by
    intro k; let H(a:U!):= a.snd.fst; let f:=fun a:U!=> (a.snd.snd,E (H a)); let S:=Finset.univ.filter fun i:U!=> o i=k
    have he(j i:J): c j=c i→ j=i:= fun h=> Finset.card_le_one.mp (ht (c i)) j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,h⟩) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,rfl⟩)
    refine (Finset.card_image_of_injOn (s:=S) (f:=f) (fun i hi j hj h=>?_)).symm.trans_le (Finset.card_le_univ _)
    have hu: i.snd.snd=j.snd.snd:= congr_arg Prod.fst h; have hv:E (H i)=E (H j):=congr_arg Prod.snd h; have hp:o i=o j:=((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2).symm; refine Prod.ext (Subsingleton.elim ..) (Prod.ext (he _ _ ?_) hu)
    rcases i with ⟨_,x,a⟩; rcases j with ⟨_,x',a'⟩; change a=a' at hu; subst a'; change E x=E x' at hv
    cases a with
    | inl w=> cases w with
              | none=> exact hp
              | some i=> change affine (E x).1 _ _= affine (E x').1 _ _ at hp; unfold affine at hp; rw [hv] at hp; exact add_left_cancel hp
    | inr w=> exact hp
-- orientation link.Price sticker.
end spacing
end YM.RG05Readout.Halls
