import YM.FormalBulk08.Roof.Lattice

/-! Graph prescription at one step – prepare Ver, check T filtered and
invert symbolically. This has all-order pointwise algebra (finite truncations
control estimates later), no blocks for actual sectors. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d m i l e u D r j t:ℕ}{K:KernelChoices}{x: Loc G 1}
lemma soon (Y:Anthem D G)(hy: Wade x Y l)(P:Flight j t)(V:Lodge P.patch)(ρ:ChartRatio G)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)(hw:Vivid W)(hr:LocalRatio ρ)(p: Studio D)(d u): quick P V W Y ρ h hL d u p 0 l= blade P K V Y d 0 l hL p:= by
    unfold quick Grail.blade; simp_rw [Pi.smul_apply,Finset.sum_apply]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; let Z:= stepsong P Y hL p i; let T:= border P V W Z ρ h; unfold braise;rw [Finset.sum_eq_single 0]; swap
    · intro v _ hv; have he: T v 0 l=0:= by
          by_contra he; have hP: Young Z l:=step_can x P Y hy hL p i; have ht:= (youth_egg _ (convict P V Z (K:=K) hP) (fairy W ρ P V K hw hr) v 0 l he).2; omega
      change jetty _ (T v 0 l)=_;rw [he];rfl
    swap; · simp
    rw [border, dipper_first];rfl
-- θ chosen after this single step only for identity here, not for top-right bounds later.
lemma pearl_credit (F:Frame G d)(Y:Anthem D G)(hv:Clef x Y l)(σ:ℝ)(hσ:0<σ)(q:ℕ)(r:ℕ)(h:∀ i: Letter F, Pose.weight F i < q→ slots F i=r→coeff 0 (echo F Y i)=0) : Bonds F x σ q 0 r Y 0:= by
    obtain ⟨B,hB,H⟩:=victual F x 0 r q l D (η:=σ) (σ:=3*σ) (by linarith) hσ.le; have ht:= H Y hv 0 ⟨le_rfl,fun _ hy=>by omega⟩ h; rwa [mul_zero] at ht
lemma migration_peak (ρ:ChartRatio G)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)(Y:Anthem D G)(hy:Wade x Y l)(w: Vivid W)(ht:LocalRatio ρ)(p:Studio D): migrates a P V K W ρ h hL d u Y p 0 l= blade P K V Y d 0 l hL p:= (paid_nil _ _ _ _ (book_fresh _) (book_guard _)).trans (soon Y hy P V ρ h hL W w ht p d u)
lemma tip_top (F:Frame G d)(ρ:ChartRatio G)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(hd:d≤j)(ht:4≤t)(H:Hol G)(W:Pot G)(Y:Anthem D G)(i : Letter F)(hy:Clef x Y (slots F i))(q:ℕ)(h':∀ j:Letter F,Pose.weight F j< q→ slots F j=slots F i→coeff 0 (echo F Y j)=0)(hp:d<D)(hD:q≤d)(w: Vivid W)(hr:LocalRatio ρ)(hi:Pose.weight F i≤q)(u):
    coeff 0 (echo F (migrates a P V K W ρ h hL d u Y) i)=heightK P.L d (Pose.weight F i)* coeff 0 (echo F Y i):= by
    let n:=Pose.slots F i
    obtain ⟨σ,A,hσ,ha,T⟩:=hy.fare.2.2 0 n; obtain ⟨η,B,hη,hb,hB⟩:= aone P (K:=K) G ht
    let z:=min η (P.L.val*σ); have hz:0<z:= lt_min hη (mul_pos (by positivity) hσ); have hZ:= strip_mono hB (min_le_left (b:=P.L.val*σ) η) le_rfl; have hU:= pearl_credit F Y hy _ hσ q n h'
    obtain ⟨C,hc,Hx⟩:= Lodge.bothPay G K V z hz; have hx:= Hx _ _ hb hZ
    rw [echo_nil,echo_nil, migration_peak ρ a P V h hL W Y hy.fare w hr,show blade P K V Y d 0 (slots F i) hL (inside F i D)=towerV (chair P G K) Y d 0 (slots F i) hL (inside F i D) from ?_]; swap
    · have hh := tollgate x P V d 0 n K Y _ hy B (C * B) (C*B) hZ hb hx.1 hx.2.1 hz (min_le_right ..) hσ.le (show 0≤(0:ℝ) from le_rfl) T hU.2.1 hL (inside F i D); rw [mul_zero,zero_mul] at hh; exact sub_eq_zero.mp (lease_cut x _ hh)
    exact council x F Y hy q hp hD i rfl hi P hd ht H K hσ hU hL (fun j=>⟨_,T j⟩) hz (min_le_right ..) hZ hb
lemma height_install (L:Side)(k:ℕ):0<heightK L d k:= mul_pos (by positivity) (pow_pos Dawn.scale_pos _)
structure Court (o: Loc G 1)(F:Frame G d)(Y:Plaza F D): Prop where
    officers (x:Letter F): Clef o (Y x) (slots F x)
    salary: pantry F Y=1
variable {F:Frame G d}
lemma Court.city {Y: Plaza F D}(h:Court x F Y) (i j): echo F (Y j) i= if i=j then 1 else 0:= (congr_fun (congr_fun h.salary i) j).trans Matrix.one_apply
lemma performed (o:Loc G 1)(F:Frame G d)(Y: Plaza F D)(ρ:ChartRatio G)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)(H:Hol G)(hp:d<D)(hd:d≤j)(ht:4≤t)(hv:Story W (pink K.penalty P.wing))(hw:LocalRatio ρ)(hy:Court o F Y) :
   Colfax (slots F) (Pose.weight F) (pantry F (migrates a P V K W ρ h hL d d ∘ Y)) (fun i=> heightK P.L d (Pose.weight F i)):= by
   let N:=migrates a P V K W ρ h hL d d ∘ Y; have hN i: Clef o (N i) (slots F i):=migrate_w a h hL d (hy.officers i) hv ht hw (slotsFits F _)
   refine ⟨fun i j e he=>voice_yields F (hN j).fare i e he,fun i=>height_install ..,fun i j he hP=>?_⟩
   have hh : Clef o (Y j) (slots F i):= he.symm ▸ hy.officers j
   have he' (z:Letter F)(h:Pose.weight F z<Pose.weight F j): z≠j:= fun he=>by rw [he] at h; exact Nat.lt_irrefl _ h
   have hk := tip_top F ρ a P V h hL hd ht H W (Y j) i hh (Pose.weight F j) (fun z h _=>by rw [hy.city z j, if_neg (he' z h),map_zero]) hp (weightFits F j) hv.toVivid hw hP d
   change coeff 0 (echo F (N j) i)=_; unfold N; simp only [Function.comp_apply]; rw [hk,hy.city]; by_cases h:i=j<;>simp [h]
lemma topC (o:Loc G 1)(F:Frame G d)(T:SectionData F)(H:Hol G)(h:T.Sound H)(hp:Bid.pop T)(ht:d+1≤D) : Court o F (sectionY T ht):= by
    refine ⟨opens T ht o H h hp,?_⟩
    ext1 i j; unfold pantry; rw [chairs T H o h hp ht j i, Matrix.one_apply]; split <;> rename_i he <;> simp [he,Ne.symm]
end YM.FormalBulk08.Roof
