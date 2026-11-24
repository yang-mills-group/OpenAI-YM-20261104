import YM.Next.EXTRACTION.Base
import YM.UVExt.BaseStep
import YM.Work.D04

set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open YM.Bid Set Filter Function MeasureTheory Extraction Extraction.Lease Dash Wilson Table
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}

/-! ### Copy/adapt the D04 transfer lemmas to keep control of the *particular* vetted vector x. -/
lemma sober_of_cont {P : Trial C} (h : ∀ N p x, Continuous (P N p x)) :
    sober C P F := by
  apply (Order.fused F (fun j => ∀ x, Measurable (P j.1 j.2 x) ∧
    ∃ A : ℝ, ∀ v, ‖P j.1 j.2 x v‖ ≤ A)).mp
  exact Eventually.of_forall fun (N,p) x =>
    ⟨(h N p x).measurable,
      (h N p x).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩

private lemma sober_upper {e : ℕ} (w : Rowe C e) : sober C (upper C w) F :=
  sober_of_cont fun N p x => C.continuousO N p e (w (N,p)) x

private lemma separate_slot (P : Trial C) (v : Shot C.book) (N p : ℕ)
    (z : Fin v.n → Lattice.Site (C.side N p)) :
    featuring P v.left v.i N p z = moment (C.beta N p)
      (fun U => P N p (z v.i) U * ∏ j ∈ Finset.univ.erase v.i, C.seen (v.left j) (z j) U) := by
  unfold featuring
  congr 1
  funext U
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.i), if_pos rfl]
  congr 1
  exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

/-- Splitting uses *integrable* moments. Trials used together here are
measurable bounded at each site (eventually; bound can depend on cutoff, period,
site); so are their differences. -/
private lemma target_sub {P Q : Trial C} (hp : sober C P F) (hq : sober C Q F)
    (v : Shot C.book) :
    ∀ᶠ u in F.fuse, targetB (P-Q) v u.1 u.2 = targetB P v u.1 u.2 - targetB Q v u.1 u.2 := by
  rw [Order.fused, Order.late]
  unfold sober Order.late at hp hq
  filter_upwards [hp, hq] with i hi hi'
  filter_upwards [hi, hi'] with j h h'
  let N := F.mesh j
  let p := F.per i
  change targetB (P-Q) v N p = targetB P v N p - targetB Q v N p
  unfold targetB
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_sub]
  congr 1
  rw [separate_slot, separate_slot, separate_slot]
  let R := fun U : Config G (C.side N p) =>
    ∏ j ∈ Finset.univ.erase v.i, C.seen (v.left j) (z j) U
  have hc : Continuous R := continuous_finsetProd _ fun b _ =>
    C.continuousO N p (v.left b).1 (v.left b).2 _
  have hR : Integrable R (law G _ (C.beta N p)) := continuous_integrable _ hc
  have H (T : Config G (C.side N p) → ℂ) (hT : Measurable T ∧ ∃ A : ℝ, ∀ U, ‖T U‖ ≤ A) :
      Integrable (fun U => T U * R U) (law G _ (C.beta N p)) := by
    obtain ⟨hm,A,hA⟩ := hT
    exact hR.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hA)
  unfold moment
  rw [← integral_sub (H _ (h (z v.i))) (H _ (h' (z v.i)))]
  apply integral_congr_ae
  filter_upwards with U
  change (P N p (z v.i) U - Q N p (z v.i) U) * R U = _
  rw [sub_mul]

private lemma upper_scan {e : ℕ} (w : Rowe C e) (v : Shot C.book) (N p : ℕ) :
    targetB (upper C w) v N p = snapshots v e (N,p) (w (N,p)) := by
  change targetB _ v N p = Order.smears C N p (v.record (d := e) (w (N,p))) v.f
  unfold targetB Order.smears
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [Family.num]; unfold featuring moment
  apply integral_congr_ae
  filter_upwards with U
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = v.i
  · subst j
    rw [if_pos rfl, Shot.record, update_self]
    rfl
  rw [if_neg h, Shot.record, update_of_ne h]

/-- Transfer of tested values between sober trials with the actual rent on
P-Q. Use the centered book with Lease.take, don't treat point convergence as
covering projection ties. -/
private lemma follow (W : YM.Bid.D02) (h : C.Makes) (c : CenterPort C F)
    {P Q : Trial C} (hp : sober C P F) (hq : sober C Q F)
    (he : YM.Bid.close C F (P-Q)) (v : Shot C.book) {L : ℂ}
    (hL : Tendsto (uncurry (targetB Q v)) F.fuse (𝓝 L)) :
    Tendsto (uncurry (targetB P v)) F.fuse (𝓝 L) := by
  obtain ⟨y, hy, hr⟩ := he
  have ht := W h c (P-Q) ⟨y,hy,Lease.take h (c.book _ _) hr⟩ v
  have ha := ht.add hL
  rw [zero_add] at ha
  apply ha.congr'
  filter_upwards [target_sub hp hq v] with u hu
  change targetB (P-Q) v u.1 u.2 + targetB Q v u.1 u.2 = _
  rw [hu, sub_add_cancel]; rfl

private lemma marked_silent (W : YM.Bid.D02) (h : C.Makes) (c : CenterPort C F)
    {e : ℕ} (R : Bin S) (hx : RelayBin C R F e) (x : Rowe C e)
    (hr : ∀ j, (R e).step j (x j) = 0) (hd : dollar C F x) (i : Shot C.book) :
    Tendsto (fun u => snapshots i e u (x u)) F.fuse (𝓝 0) := by
  obtain ⟨z,hz,he,hb⟩ := hx.mark x hr hd
  have hg : gain z F (fun _ _ => 0) := by
    intro n q j δ hδ
    refine ⟨0, le_rfl, ?_⟩
    have hm := he n q j δ hδ
    unfold Order.late at hm ⊢
    filter_upwards [hm] with r hm'
    filter_upwards [hm'] with s hs x H
    rw [hs x H]; simp
  have ha := W h c z ⟨_, tendsto_const_nhds, hg⟩ i
  refine (follow W h c (sober_upper x) hz hb i ha).congr' (Eventually.of_forall ?_)
  rintro ⟨N,p⟩
  exact upper_scan x i N p

/-! ### Paying only top-coordinate costs -/

private lemma dollar_shrink {e : ℕ} {x : Rowe C e} (h : dollar C F x)
    (b : ℕ × ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ 1) :
    dollar C F (fun j => b j • x j) := by
  intro ε hε
  have ht := h ε hε
  unfold Order.late at ht ⊢
  filter_upwards [ht] with p hp
  filter_upwards [hp] with j hj
  rw [map_smul, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb _)).trans hj

lemma dollar_sub {e : ℕ} {x y : Rowe C e} (hx : dollar C F x) (hy : dollar C F y) :
    dollar C F (d := e) (fun j => x j-y j) := by
  intro ε hε
  have hr := hx _ (half_pos hε)
  have hs := hy _ (half_pos hε)
  have hm : Tendsto (fun j : ℕ => Real.exp ((ε/2)*C.S.scale (F.mesh j))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((C.S.divergent.comp F.mesh.cofinal).const_mul_atTop (half_pos hε))
  unfold Order.late at hr hs ⊢
  filter_upwards [hr,hs] with p hp hq
  filter_upwards [hp,hq,hm.eventually_ge_atTop 2] with i ha hb hi
  rw [map_sub]
  refine (norm_sub_le _ _).trans ((add_le_add ha hb).trans ?_)
  let s := C.S.scale (F.mesh i)
  change Real.exp ((ε/2)*s) + Real.exp ((ε/2)*s) ≤ Real.exp (ε*s)
  change 2 ≤ Real.exp ((ε/2)*s) at hi
  rw [show ε*s = (ε/2)*s + (ε/2)*s by ring, Real.exp_add]
  nlinarith [Real.exp_pos ((ε/2)*s)]

/-- x itself need not be tight. Normalize both pieces by the size of the
projected piece; this is enough to use mark on the normalized remainder. -/
private lemma cost_limit (T : YM.Bid.D01) (W : YM.Bid.D02) (h : C.Makes)
    (c : CenterPort C F) (R : Bin S) {e : ℕ} (H : RelayBin C R F e)
    {x : Rowe C e} (hx : dollar C F x) (i : Shot C.book) :
    Tendsto (fun u => snapshots i e u (x u - (R e).step u (x u)) /
      (1 + (↑‖(R e).step u (x u)‖ : ℂ))) F.fuse (𝓝 0) := by
  let p : Rowe C e := fun u => (R e).step u (x u)
  let a (j : ℕ × ℕ) := (1+‖p j‖)⁻¹
  let b (j : ℕ × ℕ) := (↑(a j) : ℂ)
  let z : Rowe C e := fun j => b j • (x j-p j)
  have hn (j) : ‖b j‖ = (1+‖p j‖)⁻¹ := by
    unfold b a
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb (j) : ‖b j‖ ≤ 1 := by
    rw [hn, ← one_div]
    exact (div_le_one (by positivity)).mpr (by simp)
  have ht : tight C F (d := e) (fun j => b j • p j) := by
    refine ⟨1,?_⟩
    apply (Order.fused F (fun j => ‖b j • p j‖ ≤ 1)).mp
    refine Eventually.of_forall fun j => ?_
    rw [norm_smul, hn, mul_comm, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hz : dollar C F z := by
    have he := dollar_sub (dollar_shrink hx b hb) (T C h e F _ ht)
    simpa only [z, smul_sub] using he
  have hk (j) : (R e).step j (z j) = 0 := by
    simp only [z, p, map_smul, map_sub, (R e).projection, sub_self, smul_zero]
  apply (marked_silent W h c R H z hk hz i).congr'
  filter_upwards with j
  rw [show z j=_ • (x j-p j) from rfl,map_smul,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm, show b j = (↑((1+‖p j‖)⁻¹) : ℂ) from rfl,
    Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one]

/-!
Main new observation: Along the SAME extraction, the full test limits and the lower rank shortage
keep the matched physical projection *bounded*. Thus first normalized discrete differences
are approximated (for one differentiated insertion among arbitrary undifferenced primary
spectators) by correlators of primaries up to a fixed weight with uniformly bounded coefficients,
off the physical coincidence diagonals. All bounds here are initially eventual for the period
then mesh extraction.
-/

lemma projection_bounded {V U Y : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {ℱ : Filter U} [ℱ.NeBot] (S : Dash.Branch V U) (P : U → V)
    (f : Y → U → V→L[ℂ]ℂ) (g : Y → V →L[ℂ] ℂ) {q : Y→ℂ}
    (ha : Dash.approaches ℱ S) (hV : verified S g) (hg : ∀ i, Tendsto (f i) ℱ (𝓝 (g i))) (hA : Dash.Added q P S ℱ f) :
    ∃ A:ℝ, ∀ᶠ n in ℱ, ‖S.step n (P n)‖ ≤ A := by
  let p n := S.step n (P n); let s n := 1+‖p n‖; let w n := (↑((s n)⁻¹):ℂ) • p n
  have hW n : ‖w n‖ ≤ 1 := by unfold w s; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity), inv_mul_eq_div]; apply div_le_one (by positivity)|>.mpr; linarith
  by_contra! h
  let L := ℱ ⊓ comap s atTop
  haveI : NeBot L := inf_neBot_iff.mpr fun A hA B hB => by
    obtain ⟨B',hb',h'b⟩ : ∃ B' ∈(atTop:Filter ℝ), s ⁻¹' B'⊆ B := hB
    obtain ⟨N,hN⟩:= eventually_atTop.mp hb'
    change ∀ b≥N,b∈B' at hN
    obtain ⟨n,hA',hn⟩ := ((h N).and_eventually hA).exists
    exact ⟨n,hn,h'b (hN (s n) (by unfold s p; linarith))⟩
  have hs : Tendsto s L atTop := by apply tendsto_iff_comap.mpr inf_le_right
  obtain ⟨v,hv,hc⟩ := (isCompact_closedBall (0:V) 1).exists_mapClusterPt_of_frequently
      (Eventually.frequently (f:=L) (p:=fun n=> w n ∈ Metric.closedBall (0:V) 1) (Eventually.of_forall (fun n => by simpa only [Metric.mem_closedBall,dist_zero_right] using hW n)))
  obtain ⟨W,hSub,hw⟩ := mapClusterPt_iff_ultrafilter.mp hc
  let T : Filter U := W
  haveI : NeBot T := Ultrafilter.neBot W
  have hw : Tendsto w T (𝓝 v) := hw
  have hTL : T≤L:= hSub
  have he : T ≤ ℱ := le_trans hTL inf_le_left
  have hq := tendsto_inv_atTop_zero.comp (hs.mono_left hTL)
  have hK (i : Y) : g i v=0 := by
    apply tendsto_nhds_unique (arcing ((hg i).mono_left he) hw)
    refine Tendsto.congr' ?_ (show Tendsto
      (fun n=> ((↑((s n)⁻¹):ℂ)*f i n (P n)) - f i n (P n-p n)/(s n:ℂ)) T (𝓝 _) from ?_)
    · filter_upwards with n; change _=(f i n) (w n); unfold w; rw [map_smul,smul_eq_mul]; push_cast; rw [map_sub]; ring
    convert (((Complex.continuous_ofReal.tendsto _).comp hq).mul ((hA.meets i).mono_left he)).sub ((hA.costly i).mono_left he) using 1
    · funext x; simp [s,p]
    push_cast; simp only [zero_mul, sub_zero]
  have hC : S.trueP v=v := tendsto_nhds_unique_of_eventuallyEq (arcing (ha.mono_left he) hw) hw
    (Eventually.of_forall (fun n=> by change S.step n (w n)=w n; unfold w p; rw [map_smul,S.projection]))
  have hz : v=0 := hC.symm.trans ((hV.symm ▸ ((Submodule.mem_iInf _).2 (fun i => (LinearMap.mem_ker).mpr (hK i)))) : v∈LinearMap.ker S.trueP.toLinearMap)
  rw [hz] at hw
  have hh := tendsto_nhds_unique_of_eventuallyEq (hw.norm.add hq) tendsto_const_nhds (Eventually.of_forall (fun n => by
    show ‖w n‖+(s n)⁻¹=(1:ℝ); unfold w s; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]; field_simp; ring))
  norm_num at hh

lemma bounded_fit {e : ℕ} {R : Bin S} (hc : C.Makes) (hx : CenterPort C F) (hh : F.Ordered C S)
    {h : Live S} (hS : RelayBin C R F e) (hd : Bin.Good R h e) {P : Trial C} (hs : sober C P F)
    {m : Dash.Shot C.book →ℂ} (hL : ∀ v,Tendsto (uncurry (targetB P v)) F.fuse (𝓝 (m v)))
    (x : Rowe C e) (hx₀ : dollar C F x) (hF : Bid.close C F (upper C x-P)) :
    ∃ A : ℝ, F.late fun n p=> ‖(R e).step (n,p) (x (n,p))‖ ≤ A := by
  let f := fun i : Shot C.book => snapshots i e; let g := fun i : Shot C.book => i.core (d:=e) S h
  have h' : Added m x (R e) F.fuse f := by
    refine ⟨fun i=> ?_,cost_limit Work.D01.answer Work.D02.answer hc hx R hS hx₀⟩
    exact (follow Work.D02.answer hc hx (sober_upper x) hs hF i (hL i)).congr (fun u => upper_scan x i u.1 u.2)
  obtain ⟨A,hA⟩ := projection_bounded (R e) x f g hS.P hd (fun i=> i.ready h hh _) h'
  exact ⟨A,(Order.fused F _).mp hA⟩

/-- At every separated tuple, a one-slot normalized difference whose fixed-output vector
has been vetted is close to an *eventually bounded* vector tested in the same slot. Budget on a
single distinguished insertion, not products of several differences. -/
def approximable (C : Family G) (F : Extraction.Order) (d : ℕ) (P : Trial C) (x : Rowe C d) : Prop :=
  tight C F x ∧ ∀ n (q : Fin n→C.book.Token) (i:Fin n) (δ ε : ℝ), 0<δ → 0<ε → F.late fun N p =>
    ∀ z : Fin n→YM.Lattice.Site (C.side N p), (∀ i j:Fin n,i≠j → δ ≤ C.S.a N * Lattice.separation (z i) (z j)) →
          ‖featuring P q i N p z-featuring (upper C x) q i N p z‖ ≤ ε

private lemma split_feature (P : Trial C) {n N p} (q : Fin n → C.book.Token) (i : Fin n) (z) :
    featuring P q i N p z= moment (C.beta N p) (fun U=>P N p (z i) U* ∏ j ∈ Finset.univ.erase i, C.seen (q j) (z j) U) := by
  unfold featuring; congr 1; ext U; rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_pos rfl]; congr 1
  exact Finset.prod_congr rfl fun j hj=>if_neg (Finset.ne_of_mem_erase hj)

private lemma feature_sub {P Q : Trial C} (hP : sober C P F) (hQ : sober C Q F) {n} (q : Fin n→C.book.Token) (i : Fin n) :
    F.late fun N p=> ∀ z, featuring (P-Q) q i N p z = featuring P q i N p z - featuring Q q i N p z := by
  dsimp [sober,Order.late] at hP hQ ⊢
  filter_upwards [hP,hQ] with j hj ht
  filter_upwards [hj,ht] with k hp hq z
  let N:=F.mesh k;let p:=F.per j; let D := fun U:Config G (C.side N p)=>∏ j∈Finset.univ.erase i,C.seen (q j) (z j) U
  have hd : Integrable D (law G _ (C.beta N p)) := continuous_integrable _ (continuous_finsetProd _ fun j _=> C.continuousO ..)
  have hi (R : Config G (C.side N p)→ℂ)(h : Measurable R ∧ ∃ b:ℝ,∀ U,‖R U‖ ≤ b) : Integrable (fun U=>R U*D U) (law G _ (C.beta N p)):= by
    obtain ⟨hm,b,hb⟩ := h; exact hd.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hb)
  simp_rw [split_feature,moment]; rw [←integral_sub (hi _ (hp (z i))) (hi _ (hq (z i)))]
  exact integral_congr_ae (Eventually.of_forall (fun U => by show _*D U=_; change (P N p (z i) U-Q N p (z i) U)*D U = _;rw [sub_mul]))

private lemma close_feature (C : Family G) (hf : C.Makes) (hc : CenterPort C F) {R : Trial C} (h : Bid.close C F R) :
    ∀ n (q : Fin n→C.book.Token) (i : Fin n) (δ ε :ℝ), 0<δ → 0<ε → F.late fun N p=>
      ∀ z, (∀ i j : Fin n,i≠j → δ ≤ C.S.a N * Lattice.separation (z i) (z j)) → ‖featuring R q i N p z‖ ≤ ε := by
  obtain ⟨y,ht,he⟩:=h; intro n q i δ ε hδ hε
  obtain ⟨b,hb,h⟩ := Lease.take hf (hc.book ..) he n q i δ hδ
  have HH := Order.fused F _ |>.mp (ht.eventually (ge_mem_nhds (by positivity : (0:ℝ)<ε/(b+1))))
  dsimp [Order.late] at HH h ⊢; filter_upwards [h,HH] with j ht hh'; filter_upwards [ht,hh'] with k hk hy z hz
  exact le_trans (hk z hz) (by change b* _ ≤ _; rw [le_div_iff₀ (by linarith)] at hy; have hx := norm_nonneg (featuring R q i (F.mesh k) (F.per j) z)|>.trans (hk z hz); nlinarith)

lemma obtain_match {e : ℕ} {R : Bin S} (hc : C.Makes) (hx : CenterPort C F) (hh : F.Ordered C S)
    {h : Live S} (hS : RelayBin C R F e) (hd : Bin.Good R h e) {P : Trial C} (hs : sober C P F)
    {m : Shot C.book →ℂ} (hL : ∀ v,Tendsto (uncurry (targetB P v)) F.fuse (𝓝 (m v)))
    (he : vet C F e P) : ∃ w, approximable C F e P w := by
  obtain ⟨x,h_cost,hxz⟩:=he
  let w n := (R e).step n (x n)
  have hM := bounded_fit hc hx hh hS hd hs hL x h_cost hxz
  refine ⟨w,hM,fun n q i δ ε hδ hε => ?_⟩
  let y n := x n - w n
  obtain ⟨z,hz,he,hoz⟩:=hS.mark y (fun n => by simp only [y,w,map_sub,(R e).projection,sub_self])
    (dollar_sub h_cost (Work.D01.answer C hc _ _ _ hM))
  have hy := close_feature _ hc hx hoz _ q i δ (ε/2) hδ (half_pos hε)
  have hv := close_feature _ hc hx hxz _ q i δ (ε/2) hδ (half_pos hε)
  have hz₀:= he _ q i δ hδ; have h₁:=feature_sub (sober_upper x) hs q i; have h₂:=feature_sub (sober_upper y) hz q i;
  have h₃:=feature_sub (F:=F) (sober_upper x) (sober_upper w) q i
  dsimp [Order.late] at hy hv hz₀ h₁ h₂ h₃ ⊢
  filter_upwards [hy,hv,hz₀,h₁,h₂,h₃] with j hy hv hz₁ h₁ h₂ h₃
  filter_upwards [hy,hv,hz₁,h₁,h₂,h₃] with t hu hw hz₀ ht hs hv a ha
  let N:=F.mesh t; let p:=F.per j
  let L (P : Trial C) := featuring P q i N p a
  have hf_ : upper C x - upper C w = upper C y := by
    funext N p o U; change C.O N p (x _) o U - C.O _ _ _ _ _ = C.O _ _ (y _) _ _
    exact (congr_fun (C.linearO N p _ o|>.map_sub _ _) _).symm -- copy from D01?
  rw [hf_] at hv
  show ‖L P-L (upper C w)‖≤ε
  simp_rw [show L P-L (upper C w)=L (upper C y-z)-L (upper C x-P) from by
    unfold L; dsimp [N,p]; rw [ht,hs,hz₀ _ ha,hv,sub_zero]; ring]
  linarith [norm_sub_le (L (upper C y-z)) (L (upper C x-P)), hu _ ha,hw _ ha]

end YM.UVExt
