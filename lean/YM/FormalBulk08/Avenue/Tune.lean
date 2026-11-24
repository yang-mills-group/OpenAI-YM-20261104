import YM.FormalBulk08.Avenue.Cover
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
variable {I:Type}{τ:Time I}{Z T:I→ Beams (edgeL G)}
variable {δ B Q σ g:I→ℝ} {A L:I→edgeL G→edgeL G→ℝ}
lemma grand_staff (h:Soft τ B)(hp:∀ i,0≤ B i)(hs:∀ i,0≤σ i)(hb:∀ x i j,‖A x i j‖≤ B x){T:I→Studio D→ Tile (edgeL G) (r+2)}(hh:Tender τ o σ g T): Tender τ o σ g (fun i p=>stare (A i) (T i p)):= by
   obtain ⟨C,hC,H,ht⟩:=hh;let n:ℝ:=1/2*(r+2)*(r+1); refine ⟨_,(soft_coin τ n).times (h.times hC),fun i=>mul_nonneg (by unfold n; positivity) (mul_nonneg (hp _) (H _)),fun i p=>?_⟩
   convert knox_stare (ht i p) (hs i) (hb i) (hp i) using 1; unfold n;ring
lemma beam_staff (h:Soft τ B)(hp:∀ i,0≤ B i)(hs:∀ i,0≤σ i)(hd:∀ i,0≤δ i)(hb:∀ x i j,‖A x i j‖≤ B x)(hq:∀ x i j,‖L x i j‖≤B x)(hR:∀ x i j, ‖A x i j-L x i j‖≤ B x * δ x){T S:I→Studio D→Tile (edgeL G) (r+2)}(ht:Brass τ o σ δ g T S): Brass τ o σ δ g (fun i p=>stare (A i) (T i p)) (fun i p=>stare (L i) (S i p)):= by
    obtain ⟨C,hC,a,H⟩:= ht.left; obtain ⟨M,hM,b,hU⟩:= ht.right;have he: Tender τ o σ (fun i=> δ i*g i) (fun i p=>stare (A i-L i) (S i p)):= by
       let n:ℝ:=1/2*(r+2)*(r+1); refine ⟨_,(soft_coin τ n).times (h.times hM),fun i=>mul_nonneg (by unfold n;positivity) (mul_nonneg (hp _) (b _)),fun i p=>?_⟩; convert knox_stare (q:=A i-L i) (hU i p) (hs i) (hR i) (mul_nonneg (hp i) (hd i)) using 1;unfold n;ring
    have hz:Tender τ o σ (fun i=>δ i*g i) (fun i p=> T i p-S i p):= brass_crisp ht
    refine Spruce.tenderJoin (grand_staff h hp hs hb ht.1) (grand_staff h hp hs hq ht.2) ?_
    simp_rw [show ∀ (i:I) (p:Studio D),stare (A i) (T i p)-stare (L i) (S i p)=_ from fun i p=>Quire.stove (H i p) (hU i p) (hs i) (hb i) (hq i) (hp i) (hp i)]; exact (grand_staff h hp hs hb hz).plus he
section
variable {T S:I→ Studio D→Beams (edgeL G)}
lemma stature_pay (h:Soft τ B)(hp:∀ i,0≤ B i)(hs:∀ i,0≤σ i)(hd:∀ i,0≤δ i)(hb:∀ x i j,‖A x i j‖≤ B x)(hq:∀ x i j,‖L x i j‖≤B x)(hR:∀ x i j, ‖A x i j-L x i j‖≤ B x * δ x)(ht:∀ r, Brass τ o σ δ g (fun i p=> T i p r) (fun i p=> S i p r))(l :ℕ): Brass τ o σ δ g (fun i p=>pageant (A i) (T i p) l r) (fun i p=>pageant (L i) (S i p) l r):= by
    unfold Brass pageant; apply matched_sums _; intro i _; suffices H:∀ n j,Brass τ o σ δ g (fun i p=>bleat (A i) (T i p) n j) (fun i p=>bleat (L i) (S i p) n j) from (H i r).amp (Pact.coin ..)
    intro n; induction n with
    | zero=> exact ht
    | succ n ih=> exact fun j=> beam_staff h hp hs hd hb hq hR (ih _)
end
structure Fees (G:Gauge) (K:KernelChoices) (j:ℕ) (B:ℝ): Prop where
    active:0 ≤ B
    cords: ∀ (v:Train j) (i k), ‖bandP G v K.penalty i k‖ ≤ B
    fade:∀ (A: Levels G) (N M i:ℕ),A.clock.J i=j→i≤N→ N≤M→∀ x y, ‖bandP G (location A N i) K.penalty x y-bandP G (location A M i) K.penalty x y‖≤B * ratioR A.S N i targetPower
lemma fee_goods (G:Gauge)(K:KernelChoices)(j:ℕ)(h:4≤j):∃ B:ℝ,Fees G K j B:= by
   obtain ⟨C,hC,H⟩:= press_core G K.penalty_pos h; obtain ⟨B,hB,M⟩:= press_move G K.penalty_pos h; refine ⟨C+B,add_nonneg hC hB,fun v x y=> ((H v).2 x y).trans (le_add_of_nonneg_right hB),fun a b c i p hp hx x y=> ?_⟩
   refine ((M _ _ _ _ p hp hx).2 x y).trans (mul_le_mul (le_add_of_nonneg_left hC) ?_ (fineR_pos a b i).le (add_nonneg hC hB)); rw [←ratioR_fineR a b i hp]; unfold ratioR targetPower;exact Real.rpow_le_rpow_of_exponent_ge (div_pos (Schedule.a_pos ..) (Schedule.a_pos ..)) (div_le_one_of_le₀ (Schedule.strictAnti _ |>.antitone hp) (Schedule.a_pos ..).le) (by norm_num)
variable {K:KernelChoices}
def mediumP (G:Gauge)(K:KernelChoices)(j:ℕ):ℝ:= if h:4≤j then (fee_goods G K j h).choose else 0
lemma fee_live (G:Gauge)(K:KernelChoices)(j:ℕ)(h:4≤j):Fees G K j (mediumP G K j):=by rw [mediumP,dif_pos h]; exact (fee_goods G K j h).choose_spec
open Dove.Lab
variable {X:Type}
def Extras (W:Lab G K X):Prop:= Soft (chron W.scrolls) (fun x=> mediumP G K (W.lower x))
end YM.FormalBulk08.Avenue
