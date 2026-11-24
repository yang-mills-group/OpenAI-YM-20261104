import YM.FormalBulk08.Broc.Alps

/-! Uniform linear prices for any packet expansion through chosen E. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{r t e E:ℕ}{A σ:ℝ}

lemma play_money {p:ℕ→Atom G r}(h:AtomWall p σ A):0≤A:=(tsum_nonneg h.1.1).trans h.1.2.2
-- includes discarded rank-one absent; no smooth routines assume hB stencil.
lemma play_boom (G:Gauge)(r m:ℕ)(hs:0<σ): ∃ δ K,0<δ∧0≤K∧∀ p:ℕ→Atom G r,∀ A,AtomWall p σ A→ ∃ T:Tile (edgeL G) (m+1),Bail (fame _) δ T (A*K)∧ Up T ∧ Matched T (fun n=>turnSeries p (m:=n)) := by
    obtain ⟨u,C,h,h',hp⟩:= orbit_cost G r m hs; refine ⟨u/2/2,C*radioCost G u m,by positivity,mul_nonneg h' (radio_charges _ _ h),fun p A H=>?_⟩
    obtain ⟨L,hL,H'⟩:= hp p _ H.1;have hm:= mul_nonneg (play_money H) h';rw [←mul_assoc]; exact ⟨_,radio_money hL h hm,radio_up L,radio_matched hL H' h hm⟩
lemma finance_family (u C:ℕ→ℝ)(E:ℕ)(h:∀ m,0<u m)(hp:∀ m,0≤ C m): ∃ δ K:ℝ, 0<δ ∧ 0≤K∧ ∀ j≤ E,δ≤ u j ∧ C j ≤ K:= by
    induction E with
    | zero=> exact ⟨_,_,h 0,hp 0,fun i he=> by rw [Nat.le_zero.mp he]; exact ⟨le_rfl,le_rfl⟩⟩
    | succ E ih=> obtain ⟨δ,K,hs,hx,H⟩:= ih; exact ⟨min δ (u (E+1)),max K (C (E+1)),lt_min hs (h _),hx.trans (le_max_left ..),fun i he=> by rcases lt_or_eq_of_le he with he|rfl; exact ⟨(min_le_left ..).trans (H i (by omega)).1,(H i (by omega)).2.trans (le_max_left ..)⟩;exact ⟨min_le_right ..,le_max_right ..⟩⟩

-- exact stencil profile, matches array class, includes path read at every grade
structure Freeze (T: Pot G)(p:ℕ→Atom G (t+1))(u:ℕ): Prop extends FloatK T where
    mountain:∀ n, stone T n= Broc.mountain p n u
    lives:∀ j r, T j r ≠ 0→ u≤ j ∧ r+u=t+1+j
    coins: Matched (T u (t+1)) (fun n=>turnSeries p (m:=n))
lemma given_path (G:Gauge)(hs:0<σ)(t E:ℕ): ∃ δ K:ℝ,0<δ ∧ 0≤K ∧ ∀ u:ℕ,t+1≤u+2→(t+1)%2=u%2→∀ (p:ℕ→Atom G (t+1)) A, AtomWall p σ A → ∃ T:Pot G,Freeze T p u ∧ Fits T E δ (A*K):= by
    choose f C hf hC H using fun m=> play_boom G (t+1) m hs; obtain ⟨δ,K,hδ,hK,h⟩:=finance_family f C (E+t) hf hC
    refine ⟨δ,K,hδ,hK,fun u hu hz p A Hx=> ?_⟩;choose T hb ht h' using fun m=> H m p _ Hx;have hA:=play_money Hx
    refine ⟨snowcap T t u,{snow_warm p u T hu hz Hx hs h' ht hf hb with mountain:= snow_stamp p u T hu h', lives:=?_, coins:= ?_ },mul_nonneg hA hK,?_⟩
    · intro j r he;cases r
      · exact (he rfl).elim
      next r=> unfold snowcap at he; dsimp only at he; split at he <;> first|omega| contradiction
    · rw [snowcap,if_pos ⟨le_rfl,rfl⟩];apply h'
    intro e he i;cases i
    · exact (bail_void _ δ 0).mono (mul_nonneg hA hK)
    next i=> unfold snowcap;dsimp only;split
             next hi=> have ht:=h i (by omega); exact ((hb i).shrink ht.1).mono (mul_le_mul_of_nonneg_left ht.2 hA)
             exact (bail_void _ _ _).mono (mul_nonneg hA hK)

section add
variable {T R:Pot G}{η C:ℝ}
lemma shed_stamp (hn:0≤η)(hs:0≤σ)(h:Fits T E η C)(hp:Fits R E σ A):Through E (stone (T-R) n) (stone T n - stone R n):= by
    intro e he;rw [map_sub]; simp_rw [sow_coeff,sow];rw [←Finset.sum_sub_distrib];refine Finset.sum_congr rfl fun i _=>?_; simp only [Pi.sub_apply]; rw [←map_sub];apply congr_arg; funext v; exact (funds_vat 0 n hn (h.pay e he (i+1)) _).tsum_sub (funds_vat 0 n hs (hp.pay e he (i+1)) _)
lemma vivid_plus (H:Vivid T)(h: Vivid R): Vivid (T+R):= by
    refine ⟨fun i j=> Up.add (H.civil i j) (h.civil i j),fun i j=> (H.agate i j).add (h.agate i j),fun i j he=>?_⟩
    by_cases hp:T i j=0
    · apply h.valence; intro hb; exact he (by simp only [Pi.add_apply,hp,hb,add_zero])
    exact H.valence i j hp
lemma vivid_less (H:Vivid T)(h:Vivid R): Vivid (T-R):= by
    refine ⟨fun i j=> Up.sub (H.civil i j) (h.civil i j),fun i j=> (H.agate i j).sub (h.agate i j),fun i j he=>?_⟩
    by_cases hp:T i j=0
    · apply h.valence; intro hb; exact he (by simp only [Pi.sub_apply,hp,hb,sub_zero])
    exact H.valence i j hp
lemma float_plus (H:FloatK T)(h: FloatK R): FloatK (T+R):= by
    have he n: stone (T+R) n= stone T n + stone R n:= by
       ext1 e; rw [map_add]; simp_rw [sow_coeff,sow]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> ?_; obtain ⟨η,A,h1,H1⟩:=H.fare e (i+1); obtain ⟨σ,B,h2,H2⟩:=h.fare e (i+1); rw [←map_add]; exact congr_arg _ (cum_plus 0 n h1.le h2.le H1 H2)
    refine { vivid_plus H.toVivid h.toVivid with fare:=?_, civic:=fun n=>?_ }
    · intro e i; obtain ⟨η,A,h1,H1⟩:=H.fare e i; obtain ⟨σ,B,h2,H2⟩:=h.fare e i; exact ⟨min η σ,A+B,lt_min h1 h2,(H1.shrink (min_le_left ..)).add (H2.shrink (min_le_right ..))⟩
    rw [he n]; intro s x I inst a b k ha hb hA hB hz ht hm; rw [map_add,map_add,H.civic n s x I a b k ha hb hA hB hz ht hm,h.civic n s x I a b k ha hb hA hB hz ht hm]
end add
end YM.FormalBulk08.Broc
