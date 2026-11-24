import YM.FormalBulk08.Palm.Cane

/-! Through-weights personnel and normalized label costs -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {m d l e n j t D :ℕ}{A B η σ:ℝ}{L: Side}{o:Loc G 1}
-- all sensitivity: since linear pocket cares only tile. even for m beyond d.
lemma pocket_on (F:Frame G d)(U W:Slate G d n)(m:ℕ)(c:ℝ)(he:∀ v:Fin n→ WardBin.Board G d,WardBin.depth v=m → U (WardBin.chip ∘ v)= c*W (WardBin.chip ∘ v)):
    pocket F U m=(c:ℂ) • pocket F W m:= by
    rw [←stip]; let t:=c • W; unfold Pose.pocket lent; suffices e : WardBin.tile (tide U) m=WardBin.tile (tide (c • W)) m by rw [e]
    unfold WardBin.tile; refine Finset.sum_congr rfl (fun i hi=>?_); simp only [tide_at,_root_.smul_apply,smul_eq_mul,he i (Finset.mem_filter.mp hi).2]
lemma pocket_book (F: Frame G d)(j n:ℕ)(i:F.Index) : ∃ C:ℝ,0≤C∧∀ U:Slate G d n,∀ B,0≤B → (∀ v:Fin n→WardBin.Board G d,WardBin.depth v=j → ‖U (WardBin.chip ∘ v)‖≤ B) →‖(pocket F U j i).re‖≤ C*B:= by
    let V : (Slate G d n) →ₗ[ℝ]ℝ:={toFun:= fun U=>(pocket F U j i).re,map_add':=fun x y=>by rw [bunch];rfl,map_smul':=fun t x=>by rw [stip];simp}; let s: Finset (Fin n→WardBin.Board G d):= Finset.univ.filter (fun v=>WardBin.depth v=j); let W(v:↥s) : Slate G d n→ₗ[ℝ]ℝ:={toFun:= fun U=>U (WardBin.chip∘ v.val),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}

    have hh(t:Slate G d n)(ht:∀ i,W i t=0): V t=0:= by
       change (pocket F t j i).re=0; rw [pocket_on F t 0 j 0 (fun v hv=>by rw [zero_mul]; exact ht (⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩:↥s)), Complex.ofReal_zero,zero_smul];rfl
    obtain ⟨C,hC,H⟩:= series_cap V W hh; exact ⟨C,hC,fun U B _ ht=> H U B fun i=> ht i.val (Finset.mem_filter.mp i.property).2⟩
lemma chip_gen (v: WardBin.Board G d): 0<generation (WardBin.key v):=by unfold generation;omega
lemma chip_kind (v: WardBin.Board G d): throughSlot (WardBin.chip v) (generation (WardBin.key v)):= fun k hk=> Pi.single_eq_of_ne (show k≠v.1 from fun he=> (Nat.lt_irrefl _) (he ▸ hk)) _
lemma counting (o:Loc G 1)(F:Frame G d)(l n q e D:ℕ)(hp:d<D)(hq:q≤d+1)(i:Letter F)(hz: slots F i=n)(hx:Pose.weight F i< q)(U:Side)(j t:ℕ)(hd:d≤j)(hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:0<σ):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ x:Site P.L,∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Bonds F o σ q e n Y B →(∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)→∀ η A:ℝ,0<η → η ≤ P.L.val * σ → (linesOf P K.penalty).strip η A → 0≤A →
     ‖pearlJ F (upmost P.L x (chair P G K) (Y (throughW x D hL (inside F i D)) e n)) (mint F i)‖≤ C*B:= by
    let s: Finset (Fin n→WardBin.Board G d):= Finset.univ.filter (fun v=>WardBin.depth v=Pose.label F i)
    choose! C hC HC using fun x:↥s=> badges o F n l e D q (fun i=> generation (WardBin.key (x.val i))) (fun i=>chip_gen _) _ (fun i=>chip_kind (x.val i)) (pet F i).val (show WardBin.depth x.val+ upper (pet F i).val <q from (congr_arg (·+upper (pet F i).val) (show WardBin.depth x.val=Pose.label F i from (Finset.mem_filter.mp x.property).2)).trans_lt hx) hp hq U j t hd hj ht H K hs
    let c:=∑ i,C i; have hc:0≤c:= Finset.sum_nonneg (fun _ _=> hC _); obtain ⟨a,ha,H⟩:=pocket_book F (Pose.label F i) n (mint F i)
    refine ⟨a*c,mul_nonneg ha hc,fun P h x hL Y hY B hB hp η A hη he hP hA=>?_⟩; unfold pearlJ;rw [show (F.grades (mint F i)).2=n from hz,mul_assoc]; apply H _ _ (mul_nonneg hc hB.1); intro v hv; let k:↥s:=⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩; exact (HC k P h x hL Y hY _ hB hp _ _ hη he hP hA).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=C) (fun i _=>hC i) (Finset.mem_univ _)) hB.1)
lemma traction (o:Loc G 1)(F:Frame G d)(Y:Anthem D G)(hY:Clef o Y l)(q:ℕ)(hp:d<D)(hq:q≤d)(i:Letter F)(hz: slots F i=n)(hx:Pose.weight F i≤ q)(P:Flight j t)(hd:d≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:0<σ)(hB:Bonds F o σ q e n Y 0)(x:Site P.L)(hL:2≤P.L.val)(h:∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)(hη:0<η)(he:η≤P.L.val*σ)(hX:(linesOf P K.penalty).strip η A)(hA:0≤A) :
    pearlJ F (upmost P.L x (chair P G K) (Y (throughW x D hL (inside F i D)) e n)) (mint F i)= unitStep P.L^(Pose.weight F i) * pearlJ F (Y (inside F i D) e n) (mint F i):= by
   let T:= Y (inside F i D) e n
   unfold pearlJ; rw [show (F.grades (mint F i)).2 = n from hz, pocket_on F _ (slate T d n) (F.grades (mint F i)).1 (unitStep P.L^Pose.weight F i) _]; swap
   · intro v he'; have hw: WardBin.depth v+upper (pet F i).val = Pose.weight F i:= by rw [he']; rfl
     rw [←hw]; exact heights o F q (fun i=>generation (WardBin.key (v i))) (fun _=>chip_gen _) (WardBin.chip ∘ v) (fun i=>chip_kind _) (pet F i).val (show WardBin.depth v + _ ≤ _ from hw.trans_le hx) hq hp P hd ht H K Y hY hB x hL h hs hη he hX hA
   simp [T,-Complex.ofReal_pow]
end YM.FormalBulk08.Palm
