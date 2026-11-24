import YM.FormalBulk08.Sierra.Rove
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K: KernelChoices}{T S:Pot G}{r m d D j t:ℕ}{H U:Pence}
lemma boarding (a:hue G) (T:Pot G)(h:∀ (x:edgeL G) (e r:ℕ),∃ σ A:ℝ,0<σ ∧ Knoxville (fame _) σ x (T e r) A)(hp:Young T m)(he:∀ e r, Agate (T e r)) (H U:Pence):
   let X:=stamp H U T; Young X m ∧ (∀ e r,Agate (X e r)) ∧ (∀ (x:edgeL G) (e r:ℕ),∃ σ A:ℝ,0<σ∧Knoxville (fame _) σ x (X e r) A) ∧ ∀ n,Kemp.banner m X n= Wine.canter H U (wire G n) (Kemp.banner m T n):= by
    intro X
    have hX (e r) : Agate (X e r):=Agate.sums _ fun b _=> (he b r).smul _
    have hz : Young X m:=by
       intro e r hv; by_contra ht; apply hv; apply Finset.sum_eq_zero; intro j hj;rw [show T j r=0 from Classical.byContradiction (fun hh=> by apply ht; unfold Yield; exact (hp j r hh).trans (Nat.add_le_add_left (by rw [Finset.mem_range] at hj;omega) _)),smul_zero]
    refine ⟨hz,hX,fun x e r=>?_,fun n=>?_⟩
    · choose k C hk hc using fun (i:ℕ)=>h x i r
      let I:= Finset.range (e+1); obtain ⟨a,ha,A⟩:= Finset.exists_min_image I k ⟨e,Finset.mem_range.mpr (by omega)⟩; exact ⟨k a,_,hk a,knox_sum I (fun i hi=>(penn_shrink (hc i) (A i hi)).smul (Wine.bill H U e i r))⟩
    apply banner_eq;funext i k;rw [badge X hz hX le_rfl, stamp_book]
    unfold X stamp; rw [banner_sieve (T:=fun j=> Wine.bill H U i j k • T j k) _ (fun j _=> ?hs)]; swap
    · obtain ⟨η,A,hA,hx⟩:=h (0,Exterior.coord 0,a) j k; exact (penn_total (hx.smul _) hA.le).of_norm
    refine Finset.sum_congr rfl fun j _=>?_ ; rw [sieve_smul, badge T hp he le_rfl]
-- annotate h parameter includes a: needed for nonempty. adjust
lemma stab (a:hue G)(h:Ritual T m)(hp:H*U=1): Ritual (stamp H U T) m:= by
    obtain ⟨hv,hs,hx,H⟩:= boarding a T h.health h.young h.committees H U
    refine ⟨hv,hs,hx,fun n=>?_⟩;rw [H n]; exact Wine.morph _ _ 1 0 (h.esteem n) hp
variable (P:Flight j t)(V:Lodge P.patch)(S:Pot G)(a:hue G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(hp:Story S (pink K.penalty P.wing))(hv:LocalRatio ρ)(ht:4≤t)(hT:Ritual T m)
def enterStep (k:ℕ)(T:Pot G): Pot G:= stamp (bookH (epoch a P V K S ρ h)) (bookU (epoch a P V K S ρ h)) (braise P V S T ρ h k)
include ht hp hv hT
lemma ritScore : Ritual (enterStep P V S a ρ h m T) m:= by
    let o:edgeL G:= (0,Exterior.coord 0,a); let k(n:Side):=(Classical.choice (chooseable n (n*P.patch.L) (primary P.patch K n))); exact stab a (paragon o P V S ρ h hp hv ht hT k) (book_equal _)
omit ht hp hv hT
-- move_mark = sum in e of individual. all rooted; no summability assertions on Haar.
lemma youth_shift (Y: Anthem D G)(x:Studio D)(H: 2≤P.L.val)(d u:ℕ): migrates a P V K S ρ h H d u Y x = aven P.L d • ∑ i:Site P.L, enterStep P V S a ρ h u (stepsong P Y H x i):= by
    funext e r v; unfold migrates Kemp.stir enterStep stamp quick; simp only [Pi.smul_apply, smul_eq_mul,Finset.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; apply Finset.sum_congr rfl; intro j _; rw [mul_left_comm]
include a
lemma summit (h:Ritual S m)(hp:Ritual T m): Ritual (S-T) m:= by
    have hv : Young (S-T) m:= by
        intro i j ht; by_contra hh;apply ht;change S i j-T i j=0; rw [show S i j=0 from Classical.byContradiction fun e=>hh (h.young i j e), show T i j=0 from Classical.byContradiction fun e=>hh (hp.young i j e),sub_self]
    have hH x i r:∃ η A:ℝ,0<η ∧ Knoxville (fame _) η x (S i r-T i r) A:= by obtain ⟨s,B,hs,H⟩:= h.health x i r;obtain ⟨t,C,ht,hb⟩:=hp.health x i r; exact ⟨min s t,_,lt_min hs ht,penn_sub (penn_shrink H (min_le_left ..)) (penn_shrink hb (min_le_right ..))⟩
    refine ⟨hv,fun i r=>?_,hH,fun n=>?_⟩
    · intro p s; change S i r _ - T i r _= S i r _- T i r _;rw [h.committees i r p s,hp.committees i r p s]
    have hh: Kemp.banner m (S-T) n= Kemp.banner m S n-Kemp.banner m T n:= by
       ext1 i;unfold Kemp.banner; rw [coeff_mk,map_sub, coeff_mk, coeff_mk,← Finset.sum_sub_distrib];apply Finset.sum_congr rfl; intro j ha
       change facade _ (sieve _ (S i j-T i j))=_;have hp(T:Pot G)(h:Ritual T m):Summable (T i j):= by obtain ⟨s,B,hs,hb⟩:=h.health (show edgeL G from (0,Exterior.coord 0,a)) _ _; exact (penn_total hb hs.le).of_norm -- need a
       rw [(sieve_sub_add _ (hp S h) (hp T ‹Ritual T m›)).2,map_sub]
    rw [hh]; intro I i p b k A B V X W Z U; rw [map_sub,map_sub,h.esteem n I p b k A B V X W Z U,hp.esteem n I p b k A B V X W Z U]
end YM.FormalBulk08.Sierra
