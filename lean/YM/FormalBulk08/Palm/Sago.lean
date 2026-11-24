import YM.FormalBulk08.Palm.Pelt

/-! Exact diagonal by comparison on every low slot of outer grade.
Unlike `Sector` may not put in lower Wick contractions here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {m d l e n j t D :ℕ}{A B η σ:ℝ}{L: Side}{o:Loc G 1}

lemma clear_note (v: Seasons)(x: Site L)(hL: 2≤L.val) (M: Studio D→ₗ[ℝ]ℝ)(hv:upper v<D)(h:∀ a:Spring D, upper a.val<upper v→ M (cone D a.val)=0) :
    M (throughW x D hL (cone D v))=unitStep L^upper v*M (cone D v):= by
    let k:Spring D:= ⟨v,(paper_is _).2 hv.le⟩; let U:= throughW x D hL (cone D v)
    nth_rw 1 [flag_built x hv hL]; rw [map_sum, Finset.sum_eq_single (upper v)]; swap
    · intro i hi he; unfold pamphlet; rw [map_sum]; apply Finset.sum_eq_zero; intro b hb; rw [map_smul,h];simp
      rw [show upper b.val=i from (Finset.mem_filter.mp hb).2];simp only [Finset.mem_range] at hi; omega
    swap; · simp
    unfold pamphlet; rw [map_sum,Finset.sum_eq_single k]; swap
    · intro b hb hn; have ht: upper b.val=upper v:= (Finset.mem_filter.mp hb).2
      rw [map_smul,notch_pull x _ b.val _ hL ht.ge, if_neg (show b.val ≠v from fun he=>hn (Subtype.ext he)),mul_zero,zero_smul];
    swap; · simp [peers,k]
    rw [map_smul,notch_pull x v k.val _ hL le_rfl,if_pos rfl,mul_one]; rfl
lemma shiny_zero {Y: Anthem D G}(o:Loc G 1)(F: Frame G d)(h q n:ℕ)(he:q≤d+1)(s:Seasons)(l:ℕ)(U: Fin n→Place.Potential G) (r:Fin n→ℕ)(hp:(∑ i,r i)+upper s < q)(hw:∀ i,U i∈rangeLt (Axis→G.Color) (r i))(H:Hol G)(hs:0<η)(hY:Clef o Y l)(hB:Bonds F o η q h n Y 0)(hV: Knoxville (fame _) η (0,o) (Y (cone D s) h n) A): tariffs (fun i=>assigns (U i)) (Y (cone D s) h n)=0:= by
    by_cases hz:∀ i,0<r i
    · have ht := (hypotheses o F h q n he s D l U r hz hp hw H hs).choose_spec.2 Y hY _ hB _ hV; rw [mul_zero] at ht;exact norm_le_zero_iff.mp ht
    push Not at hz; obtain ⟨i,hi⟩:= hz; have ht:=hw i; rw [Nat.le_zero.mp hi] at ht; have hh : U i=0:= Submodule.mem_bot ℝ |>.mp ht
    unfold tariffs; refine Eq.trans (tsum_congr ?_) (tsum_zero (α:=ℝ)); intro v; rw [Finset.prod_eq_zero (Finset.mem_univ i) (show assigns (U i) (v i)=0 from (by rw [hh];rfl)),mul_zero]
lemma scale_tariffs (U: Fin n→ Place.Potential G)(L:Side)(r: Fin n→ℕ)(T:Tile (edgeL G) n) : tariffs (fun i=> assigns (unitStep L^r i • U i)) T=unitStep L^(∑ i,r i)* tariffs (fun i=> assigns (U i)) T:= by
    unfold tariffs; rw [←tsum_mul_left]; apply tsum_congr; intro i; rw [show (∏ j,assigns (unitStep L^r j • U j) (i j))=∏ j,(unitStep L^r j* assigns (U j) (i j)) from rfl, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; exact mul_left_comm ..
lemma fairing {Y:Anthem D G}(o:Loc G 1)(F: Frame G d)(h q n:ℕ)(he:q≤d+1)(s:Seasons)(l:ℕ)(U W: Fin n→Place.Potential G)(r:Fin n→ℕ)(hp: (∑ i,r i)+upper s≤q)(hw:∀ i, U i∈rangeLt (Axis→G.Color) (r i))(hz:∀ i, W i-U i∈rangeLt (Axis→G.Color) (r i-1))(hr:∀ i,0<r i)(H:Hol G)(hs:0<η)(hY:Clef o Y l)(hB:Bonds F o η q h n Y 0)(hV:Knoxville (fame _) η (0,o) (Y (cone D s) h n) A):
     tariffs (fun i=> assigns (W i)) (Y (cone D s) h n)=tariffs (fun i=>assigns (U i)) (Y (cone D s) h n):= by
    let t (i:Fin n)(b:Bool):= if b then W i-U i else U i
    let k (i:Fin n)(b:Bool):= if b then r i-1 else r i; have he' (i:Fin n)(b:Bool) : t i b∈rangeLt (Axis→G.Color) (k i b):=by unfold t k;split; exacts [hz i,hw i]
    let T i b:= assigns (t i b)
    rw [show (fun i=> assigns (W i))=(fun i=> ∑ b:Bool,T i b) from funext fun i=>by rw [Fintype.sum_bool]; funext v; change _= (assigns _ v-assigns _ v)+assigns (U i) v; rw [sub_add_cancel],dial T (fun i b=>shoulder (he' i b)) hs _ hV,Finset.sum_eq_single (fun _=>false)];swap
    · intro b _ hb
      obtain ⟨j,hj⟩:=Function.ne_iff.mp hb; have hv : b j=true := Bool.eq_true_of_not_eq_false hj
      have hh : ∑ i,k i (b i)<∑ i,r i:= Finset.sum_lt_sum (fun i _=>by unfold k;split<;>omega) ⟨j,Finset.mem_univ _,by unfold k; rw [if_pos hv]; have :=hr j; omega⟩
      exact shiny_zero o F h q n he s l (fun i=>t i (b i)) _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hh _) hp) (fun i=>he' _ _) H hs hY hB hV
    swap; · simp
    rfl
end YM.FormalBulk08.Palm
