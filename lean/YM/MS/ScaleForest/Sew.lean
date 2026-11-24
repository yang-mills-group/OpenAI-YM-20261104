import YM.MS.ScaleForest.Glue

/-!
# Sew components and insert local counterterms

These rules on forests are for **ordered-scale graph families**. At a root
edge we perform one of the sewings in `Glue`, then integrate the root edge's
log length. At nonzero loop number the latter step is again a *regulated*
integration (`UV`). Subtractions are of rooted subgraphs in this convention,
with a local counterterm replacing the chosen connected subgraph. Keep the
rank (number of external half-edges of that subgraph), the engineering grade,
and the information whether the subgraph has the insertion. Always subtract
on the full `Mob`, before passing to visible four-dimensional tensors.

`Sewable`: enough to apply further integrations even for a branch carrying
uncanceled poles. `OfRank`: rank tracked before dimensional specialization.
We'll use these to establish the forest/quotient identities at the level of
**Laurent germs**, not just after subtraction of the complete series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave
open scoped Topology ContDiff

variable {G : Gauge} {K : Rip G} {F : Mob G} {b : Bool} {r u v : ℤ} {n h : ℕ} {f g : Coat G}
  {X Y J : Flats G} {z : ℂ}

/-- Use a *half*-kernel. The price and port requirements here also allow us
to do refinements (e.g. charge particular types of line separately), not
just the summed Wick kernel. No extra regulator power in the shell. -/
structure HalfKernel (K : Rip G) : Prop where
  forms (b : Bool) : Knot b K
  ghost : Credit 0 K
  real : veil K
  color : ReadyG K
  even : closedF K false
  rev : reverseF K
  falls : limp (fun t => pulse 4 t K) 0

theorem wick (G : Gauge) : HalfKernel (A0 G 0) where
  forms _ := c_bo 0
  ghost := kred G 0
  real := voile_a G 0
  color := chair_a 0
  even := cl_a G 0
  rev := reverse_a G 0
  falls := by simp_rw [pA]; exact limitA G

/-- We also track the loop zero boundary, the value needed if we
join this amplitude to something else and integrate scales there. -/
structure Sewable (b : Bool) (r : ℤ) (h : ℕ) (f : Coat G) (X : Flats G) : Prop where
  clock : ClockD b 0 r X
  start : Return X f h

abbrev OfRank (r : ℤ) (X : Flats G) := SeedP (fun f => To f (good r G)) X
abbrev collapsed (f : Coat G) : Flats G := Finsupp.single 0 f

theorem return_congr (hX : Return X f h) (he : Pact X Y) : Return Y f h := by
  unfold Return
  filter_upwards [he 0, hX] with z hz hL
  rw [← hz]
  exact hL

theorem OfRank.congr (hX : OfRank r X) (he : Pact X Y) : OfRank r Y := by
  intro i
  unfold To
  filter_upwards [hX i, he i] with z hz hL
  rw [← hL]
  exact hz

theorem OfRank.plus (hX : OfRank r X) (hY : OfRank r Y) : OfRank r (X+Y) :=
  (washed _).plus hX hY

theorem OfRank.realScale (hX : OfRank r X) (z : ℝ) : OfRank r ((z : ℂ) • X) := by
  intro i
  exact (hX i).mono fun x hx => (good r G).smul_mem (z : ℂ) hx

theorem OfRank.uses (hX : OfRank r X) (i : ℕ) : To (X i) (grade r G) :=
  (hX i).mono fun _ hz => zeroIssue hz

theorem OfRank.trim (hX : OfRank r X) (hc : ClockD b u v X) : ClockD b u r X :=
  fun i => ⟨(hc i).fine,hX.uses i⟩

theorem OfRank.nil (hX : OfRank r X) (hr : r < 0) : Pact X 0 := pact0 ⟨r,hr,hX.uses⟩

theorem collapse_rank (ht : To f (good r G)) : OfRank r (collapsed f) :=
  (washed _).single ht _

namespace Sewable

theorem congr (hX : Sewable b r h f X) (he : Pact X Y) : Sewable b r h f Y :=
  ⟨clockWind hX.clock he,return_congr hX.start he⟩

theorem plus (hX : Sewable b r h f X) (hY : Sewable b r h g Y) : Sewable b r h (f+g) (X+Y) :=
  ⟨Cap0.heap.plus hX.clock hY.clock, sip_plus hX.start hY.start⟩

theorem realScale (hX : Sewable b r h f X) (z : ℝ) : Sewable b r h ((z:ℂ) • f) ((z:ℂ) • X) :=
  ⟨fun i => (hX.clock i).smul (show star (z:ℂ) = (z:ℂ) by simp), sip_static _ hX.start⟩

theorem ofHomogeneous (hf : Cap0 b 0 r f) (hp : Count f h) : Sewable b r h f (collapsed f) :=
  ⟨Cap0.heap.single hf _, sip_root hp⟩

theorem lower (hX : Sewable true r h f X) : Sewable b r h f X := by
  cases b
  · exact ⟨fun i => ⟨(hX.clock i).fine.tire, (hX.clock i).cap⟩,hX.start⟩
  exact hX

theorem bridge (hX : Sewable b r 4 f X) (hY : Sewable b u h g Y) (hK : HalfKernel K) :
    Sewable b (r+u-2) h 0 (bridgePages K X Y) := by
  rw [bridgePages_eq hK.rev]
  have ht : Blazing b 0 (TreeN K X Y) := Fine.HeapF.explo _ _ _ (fun i j => by
    simpa using (hX.clock i).fine.wood (hY.clock j).fine (hK.forms _) hK.even hK.real hK.color hK.rev hK.ghost)
  refine ⟨fun i => ⟨ht i, capA (clockCap hX.clock) (clockCap hY.clock) hK.rev i⟩, ?_⟩
  have hx := sipair (h:=h) hX.start hY.start hK.rev 4 (by norm_num) hK.falls
  rwa [zeroA] at hx

theorem loop (hX : ClockD b 0 r X) (h : ℕ) (hK : HalfKernel K) : Sewable b (r-2) h 0 (closePages K X) := by
  have H : Blazing b 0 (CycleN K X) := Fine.HeapF.pipe _ _ _ (fun i => by
    simpa using (hX i).fine.eye (hK.forms _) hK.real hK.color hK.ghost)
  refine Sewable.congr (X := CycleN K X) ?_ (pact_sym (closePages_pact (hK.forms _) (clockMoon hX)))
  refine ⟨fun i => ⟨H i,capC r (clockCap hX) (clockMoon hX) (hK.forms b) i⟩,?_⟩
  unfold Return CycleN
  rw [bland zero_lt_one]
  simp_rw [Pi.zero_apply,← cert,map_zero]
  exact .of_forall fun _ _ _ => tendsto_const_nhds
end Sewable

theorem bridge_rank' (hF : Goods r F) {H : Mob G} (hH : Goods u H) (K : Rip G) :
    Goods (r+u-2) (bridgeG K F H) := by
  intro m l hx
  rw [mod_int] at hx
  unfold bridgeG
  rw [scatter_congr _ l _ (fun _ _ => (0:ℂ)) ?_]
  · exact map_zero (allocate ..)
  intro s t he
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hh := split_length he
  by_cases hS : (s.length:ℤ)+1 = r
  · rw [ranks_off hH _ (by simp; omega)]; simp
  rw [ranks_off hF _ (by simp; omega)]
  simp

theorem bridge_rank (hX : OfRank r X) (hY : OfRank u Y) (hK : HalfKernel K) : OfRank (r+u-2) (bridgePages K X Y) := by
  rw [bridgePages_eq hK.rev]
  refine (washed _).explo _ _ _ ?_
  intro i j
  apply ((hX i).and (hY j)).mono
  intro z hz
  change arbor K (X i z) (Y j z) ∈ good _ _
  rw [← bridgeG_eq hK.rev]
  exact bridge_rank' hz.1 hz.2 K

theorem loop_rank (hX : OfRank r X) (hc : ClockD b 0 r X) (hK : HalfKernel K) : OfRank (r-2) (closePages K X) := by
  refine OfRank.congr (X := CycleN K X) ?_ (pact_sym (closePages_pact (hK.forms _) (clockMoon hc)))
  refine (washed _).pipe _ _ _ ?_
  intro i
  unfold To
  filter_upwards [sunny (clockMoon hc i),hX i,high0] with z hz hL hv
  rw [swamp_spec (hK.forms _) hz hv]
  exact (good (r-2) G).smul_mem _ (goods_o hz (hK.forms _) hv hL)

theorem coal_bridge (hX : Sewable b r 4 f X) (hY : Sewable b u h g Y) (hU : Stay 4 X)
    (hV : Stay h Y) (hK : HalfKernel K) : Coal b h 0 (r+u-2) (bridgePages K X Y) :=
  ⟨(hX.bridge hY hK).clock,by rw [bridgePages_eq hK.rev]; exact StayB (a := 4) (by norm_num) (hK.forms b) hK.rev hU hV,
    (hX.bridge hY hK).start⟩

theorem coal_loop (hc : ClockD b 0 r X) (hX : Stay h X) (hK : HalfKernel K) :
    Coal b h 0 (r-2) (closePages K X) := by
  have hv := Sewable.loop hc h hK
  refine ⟨hv.clock, fun y s => ?_, hv.start⟩
  have hp := clockMoon hc
  exact Live.congr (Cit hX hp (hK.forms _) (a := 4) (by norm_num : (4:ℂ)-4 = (h:ℂ)-h) y s)
    (prom (pact_sym (closePages_pact (hK.forms _) hp)) _ _ _)

/-- One scale integral of the sewn component (largest length).
No pole projection involved. -/
def integratePages (h : ℕ) (X : Flats G) : Flats G :=
  X.sum fun i f => Finsupp.single i (fun z : ℂ => scaleIntegral z h i (f z))

@[simp] theorem scaleIntegral_zero (z : ℂ) (h i : ℕ) : scaleIntegral (G:=G) z h i 0 = 0 := by
  funext m w
  apply Tendsto.limUnder_eq
  have hb (a : ℝ) : regulated (G:=G) a 0 z h i 0 = 0 := by
    unfold regulated belowCut
    rw [show finiteIntegral a 0 (vamp z h i) (0 : Mob G) = 0 from ?_]
    · simp only [tad0,smul_zero,Finset.sum_const_zero]; simp
    funext m w; simp only [finiteIntegral, ← cert,map_zero, Pi.zero_apply]; simp
  simp_rw [hb]
  exact tendsto_const_nhds

theorem integrate_each (h i : ℕ) (X : Flats G) : integratePages h X i = fun z => scaleIntegral z h i (X i z) := by
  rw [integratePages,Finsupp.sum_apply,Finsupp.sum]
  by_cases hX : i ∈ X.support
  · rw [Finset.sum_eq_single_of_mem i hX, Finsupp.single_eq_same]
    intro j _ hv; simp [hv]
  simp_rw [Finsupp.notMem_support_iff.mp hX, Pi.zero_apply, scaleIntegral_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  exact Finsupp.single_eq_of_ne (show i≠j from fun h => hX (h.symm ▸ hj))

/-- Now we can use the filed theory's *estimates* for Mellin inversion. -/
theorem integrate_pact (hX : ClockD b 0 r X) (hr : Return X 0 h) : Pact (integratePages h X) (wheels X h) := by
  intro i
  rw [integrate_each,loopy]
  exact (uv_limit ((hX i).fine.tune.mer) (fun (hi : i=0) => hi ▸ hr)).mono fun _ hz => hz.1

theorem integrate_sewable (hX : Sewable b r h 0 X) :
    Vibe h (integratePages h X) X ∧ Sewable b r h 0 (integratePages h X) := by
  have hz := integrate_pact hX.clock hX.start
  obtain ⟨ht,hL,hE⟩ := scooter hX.clock hX.start
  exact ⟨vibe_trans ht (pact_sym hz) (fun _ => EventuallyEq.rfl), Sewable.congr ⟨hL,hE⟩ (pact_sym hz)⟩

theorem integrate_rank (hX : Sewable b r h 0 X) (hm : OfRank r X) : OfRank r (integratePages h X) := by
  intro i
  have hp := integrate_pact hX.clock hX.start i
  rw [loopy] at hp
  unfold To
  filter_upwards [hm i,hp,(clockMoon hX.clock i).mer.price,vamp_up h i] with x hx hz hw hV
  rw [hz]
  exact road (good r G) need_rank hx hw hV

/-- Determine how many Laurent coefficients to take by pole bound on the
sewn, integrated amplitude. Noncanonical junk when no continuation; used
only when we have proved meromorphicity. -/
def poleOrderBound (X : Flats G) : ℕ := open Classical in
  if he : ∃ n, Rent X n then Nat.find he else 0

theorem sufficientBound (hr : Merg X) : Rent X (poleOrderBound X) := by
  classical
  rw [poleOrderBound,dif_pos (tallP hr)]
  exact Nat.find_spec _

/-- Negative pole part used as a local vertex. `Pearl.Mint` is a finite
Laurent coefficient reader, uses ONLY strictly negative z powers. -/
def counterterm (X : Flats G) : Coat G := - Pearl.Mint (poleOrderBound X) X

theorem ct_kernel (hX : Sewable b r h 0 X) : Cap0 b 0 r (counterterm X) :=
  (mintCap hX.clock (sufficientBound (Moony.toast (clockMoon hX.clock)))).neg

theorem ct_cool (X : Flats G) : Cool (counterterm X) := (cone G).neg_mem (Pearl.minted (poleOrderBound X) X)

/-- Insert the counterterm into the **same** list-output symbol on loop page 0.
 `Return`, scaling, holomorphy of the total (at every cutoff length and mass)
 after subtraction. -/
structure WithPole (b : Bool) (r : ℤ) (h : ℕ) (X X' : Flats G) : Prop where
  sewable : Sewable b r h (counterterm X) X'
  stay : Stay h X'
  count : Count (counterterm X) h
  eq_tad (z : ℂ) : counterterm X z = Tad (counterterm X z) h

theorem pole_cancels (hX : Sewable b r h 0 X) (hv : Vibe h X J) (hp : Stay h J) :
    WithPole b r h X (X + collapsed (counterterm X)) := by
  have hr := sufficientBound (Moony.toast (clockMoon hX.clock))
  have ht (z : ℂ) : Home (counterterm X z) h := (minted_home hr hv hp z).neg
  refine ⟨by simpa only [zero_add] using hX.plus (Sewable.ofHomogeneous (ct_kernel hX) ht),
    ?_, ht, fun z => (ht z).complete ?_⟩
  · simpa only [counterterm,collapsed,sub_eq_add_neg,Finsupp.single_neg] using correspondent hr hv hp
  have H : kPrice ( (0:Mob G) - Pearl.Mint (poleOrderBound X) X z ) :=
    fall_sub (Form0.zero (b:=true)).price (Mint_price hr z)
  simpa only [counterterm, Pi.neg_apply,zero_sub] using H

theorem ct_rank (hX : Sewable b r h 0 X) (hF : OfRank r X) (z : ℂ) : Goods r (counterterm X z) :=
    (good r G).neg_mem (MintC (sufficientBound (Moony.toast (clockMoon hX.clock))) (good r G) need_rank hF z)

theorem with_pole_joint (hC : Coal b h 0 r J) :
    let X := integratePages h J
    Joint h J (X + collapsed (counterterm X)) 0 (counterterm X) := by
  obtain ⟨hV,hS⟩ := integrate_sewable (Sewable.mk hC.eye hC.force)
  intro X
  let p := counterterm X
  have ht := pole_cancels hS hV hC.real
  refine ⟨by simpa only [add_zero] using vibe_plus hV (vibe_root ht.count), ht.stay,
    Moony.toast (clockMoon ht.sewable.clock), ct_cool X, (ct_kernel hS).fine.tune.mer,
    ht.count, by simpa only [zero_add] using ht.sewable.start⟩

end YM.MS.ScaleForest
