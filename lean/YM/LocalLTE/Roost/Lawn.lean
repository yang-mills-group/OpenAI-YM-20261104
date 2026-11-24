import YM.LocalLTE.Roost.Arch
/-! Substitution diet. Coat frame feed. Key identity using Π torus directions incl arbitrary trees,
 no mask priority except Chip radius; not chart log relation on dense. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
variable {v z r Q W s y η γ B : ℝ} {j n m : ℕ}
section
variable (X:Coat T F)(x:ZipP G c f)(w : Directions G f)
lemma chosen : let Z:= dry X x; Z.input w= increment (replica S.ratio Z.V) (X.blank.lens w):=by
  intro Z; funext i; by_cases he:i∈F.trunks
  · rw [Z.sliced w i he,increment,Coat.lens,if_neg (show ¬X.blank.Hot i from (X.no_flat i).not.mpr (by simp [he])),G.mat_lieExp_zero,one_mul]; exact (if_pos (F.trunk_internal (by simpa using he))).symm
  rw [Z.viewing w i ((X.no_flat i).2 he),increment,increment,Coat.lens,if_pos ((X.no_flat i).2 he)]
lemma signal_for : (dry X x).signal w=X.blank.lens w:= by
  ext1 i; unfold signal; rw [Pi.add_apply, saved,if_pos (by
    by_cases hx:i∈F.trunks
    · exact Or.inl hx
    exact Or.inr ((X.no_flat i).2 hx)), zero_add]; rfl
lemma patch_rep (p : Stream c f) : let s:=p.1; let v:= X.blank.lens w; let V:=increment 1 x.1; let W:=replica S.ratio V
    let U':=(displacement s x.1 1, displacement s v W)
    Polar.rootface (dry X x) w ((dry X x).input w) true p.1 p.2 = Frond.ivy T X.x (choice s X.k) p.2 U':=by
  intro s v V W U'; have hz := Channel.pull_increment (a:=x.1) (W:= (1:Config G c)) (s:=s); rw [show Lattice.pull s 0 (1:Config G c) = 1 from by ext1 i; rw [Channel.charge]; simp] at hz -- edit
  let Z:= dry X x
  have hs : pull s 0 V=increment 1 (displacement s x.1 1):=hz
  have hv : pull s 0 (Z.input w)= Frond.shaft S U':=by
    have h : pull s 0 W = replica S.ratio (pull s 0 V):= by
       -- replica equiv
       exact Channel.pulls_replica .. -- edit
    rw [show Z.input w=increment W v from chosen X x w,Channel.pull_increment,h,hs]; rfl
  unfold Polar.rootface; rw [hv]; change loft T X.x (shaft S U') _ (pull s 0 V) _ _- _=_
  unfold Frond.ivy squarepot; rw [hs]; refine congr_arg₂ (·-·) rfl ?_
  refine Finset.sum_congr rfl fun i hi=> ?_
  rw [Vine.pot, if_pos (show (dry X x).selected s (spot S i) from X.blank_all _ _), strain, signal_for]
  dsimp only [U']; rw [← hz]; rfl
end
abbrev Disk (G:Gauge)(c:Side):= ℝ × Directions G c
section
variable (X:Coat T F)(z:Air f G)
local notation "E"=> Disk G c
local notation "E₀"=> ZipP G c f
def pass (p:E):E₀:=(p.2,0)
def timeΛ (p:E):= dry X (pass p)
def switchΛ (p:E):= voltage (timeΛ X p)+p.1 • X.atmos z
lemma rims (b:Directions G c)(β:ℝ):switchΛ X z (gStep β,b)= worldZ (timeΛ X (gStep β,b)) β z:= rfl
def twig (p:E):E₀ :=(p.2,X.blank.lens (switchΛ X z p))
def inputΛ (p:E):= Frond.shaft S (twig X z p)
lemma openingΛ (p:E): inputΛ X z p=(timeΛ X p).input (switchΛ X z p):=(chosen X (pass p) (switchΛ X z p)).symm
end
lemma glideGrowth {P:Teller G}(L : Side)(D: Patch)(hd: D.Branches P.bind G) {p d : ℝ→ℝ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W) (j:ℕ)(hj:1≤j){v:ℝ}(h : -(1/2:ℝ) ≤ v)(hW:v<0) (hp:Rate G L v p)(hk: Rate G L 0 d)(he:∀ᶠ x in atTop,0≤p x) : ∃ A C:ℝ→ℝ, Rate G L v A ∧ Rate G L 0 C ∧ ∀ᶠ t in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖≤p t →
    ‖switchΛ X z x‖ ≤ |A t| ∧ Brush j (|C t|) 1 (switchΛ X z) x := by
  obtain ⟨C,E,hC,hE,H⟩:= driftless P L D hd j hj hW hp he o.f
  let Z x:= (Fintype.card G.ColorIndex:ℝ)*|d x|
  let u (x:ℝ):=o.cap*Pressure.fiery G x L+C x*p x; let A x:= u x+p x*Z x; let V x:= C x+Z x
  have hu : Rate G L v u:= Rate.add ((Rate.flame (G:=G) (L:=L)).mul_left o.cap|>.weaken h) ((show 0+v=v from zero_add v) ▸ (hC.mul hp))
  have hZ : Rate G L 0 Z := ((hk.compare (v:=fun x=>|d x|) (Eventually.of_forall fun x=> (abs_abs _).le)).mul_left _)
  refine ⟨A,V,hu.add (by simpa only [add_zero] using! hp.mul hZ),hC.add hZ,?_⟩
  filter_upwards [H, hp.below hW _ zero_lt_one] with s hx hs c f S T hS U α hM F X ht hX z hY x hq
  have ha:= hM.localP _ X.blank ht hX (X.bowed (temp_nonneg _)); let M:= X.atmos z
  have hz : ‖M‖ ≤ Z s:= by refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))).2 (fun i=> color_cover (abs_nonneg (d s)) _ (fun j=> hY (i,j)))
  let E:= Disk G c; let E₀:=ZipP G c f; let K:E→L[ℝ] E₀:= (ContinuousLinearMap.snd ℝ ℝ (Directions G c)).prod 0
  have hK (y:E):‖K y‖ ≤ ‖y‖:= max_le (le_max_right ..) (by change ‖(0:Directions G f)‖≤_; rw [norm_zero]; exact norm_nonneg _)
  let q (y:E):= voltage (timeΛ X y)
  have hp (y:E)(hh:y∈closedBall 0 (p s)):Brush j (C s) 1 q y:= by
     have ht' := (hx c f S T hS hM.funds F X ht ha.sails.scale (K y) ((hK y).trans (mem_closedBall_zero_iff.mp hh))).1
     have he:= Brush.reading K ht' (e:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> by rw [one_mul]; exact hK y)); rw [one_mul] at he; exact he
  have h₀: timeΛ X (0:E)=X.blank := by unfold timeΛ pass dry; rw [show ( (0:E).snd,(0:Directions G f)).1=0 from rfl,Work.G07.at_zero_increment]; rfl
  have hw: ‖q 0‖ ≤ o.cap* Pressure.fiery G s L:=by
    unfold q; rw [h₀, ← Vine.agrees_all X.blank (show Room _ S _ X.blank.x from ht.symm ▸ hM.room) ha.placed]
    have hv: Pressure.fiery G s L=X.blank.t:=by unfold Coat.t; rw [show X.blank.x=s from ht,hM.funds.length_eq]
    rw [hv]; apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM.safety.1.le ha.sails.room.fiery.le)).2
    apply (hM.safety.2.2.2 F X.blank ht hX ha.placed).1
  let L':E→L[ℝ] (Directions G f):=(ContinuousLinearMap.fst ℝ _ _).smulRight M
  have hc:x∈ closedBall 0 (p s):=mem_closedBall_zero_iff.mpr hq; have hr:0≤p s:=(norm_nonneg _).trans hq
  have he:‖q x‖ ≤ u s:=by
    have hx : ‖q x-q 0‖≤ C s* ‖x-0‖:= (convex_closedBall _ _).norm_image_sub_le_of_norm_fderiv_le (fun x hx=> (hp x hx).smooth.differentiableAt (by exact_mod_cast (show j≠0 by omega))) (fun x hx=>by simpa only [normJ,pow_one,mul_one,norm_iteratedFDeriv_one] using! (hp _ hx).order 1 hj) (mem_closedBall_self hr) hc; rw [sub_zero] at hx
    exact le_trans (norm_le_insert' _ (q 0) -- edit
       ) (add_le_add hw (hx.trans (mul_le_mul_of_nonneg_left hq (hp _ hc).nonneg)))
  have hh: ‖L'‖≤ Z s:= ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans hz) (fun y=> by change ‖Prod.fst y • M‖≤_; rw [norm_smul,mul_comm (Z s)]; exact mul_le_mul (le_max_left ..) hz (norm_nonneg _) (norm_nonneg y))
  have h':‖L' x‖≤ p s*Z s:= (L'.le_opNorm _).trans ((mul_le_mul hh hq (norm_nonneg _) ((norm_nonneg _).trans hh)).trans_eq (mul_comm ..))
  refine ⟨((norm_add_le (q x) (L' x)).trans (add_le_add he h')).trans (le_abs_self _),?_⟩
  apply (hp x hc|>.gathering (linearB L' (h'.trans (mul_le_of_le_one_left ((norm_nonneg _).trans hz) ((le_abs_self _).trans hs))) _ zero_le_one)).climb (le_abs_self _) le_rfl; rwa [mul_one]
end YM.ConnectedActivityE6.Blaze.Vine
