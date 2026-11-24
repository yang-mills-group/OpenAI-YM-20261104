import YM.MS.Train.Profile
/-!
# Weakest symmetry level needed at Ward step.
Strong (Ghost,Color) on primary states. Separate rank.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z:Flats G}{K L E:Mob G}{f g:Coat G}{b c:Bool}{t q:ℤ}{U V:Rip G}{k m n h ℓ:ℕ}{i:ℂ}{s:ℝ}
structure Sun (b:Bool) (f:Coat G): Prop where
    mer : mer f
    dice : To f (sturdy b G)
lemma sunny (h:Sun b f): ∀ᶠ i in dotty, Form0 b (f i):= (h.mer.price.and h.dice).mono fun _ hi=> ⟨hi.1,hi.2⟩ -- i unused
lemma dollar (hp:Knot b U)(ht: Form0 b K)(hi:i∈Town): port i U K=ocean i U K:= by cases b; exact port_spec hi U hp ht; exact port_spec hi U hp.clearer ht.clearer
lemma swamp_spec (hp:Knot b U)(ht:Form0 b (f i))(hi:i∈Town) : swamp U f i= feeD i • ocean i U (f i):= by change feeD i • (port i U (f i))= _; rw [dollar hp ht hi]
lemma swamp_m (h:Sun b f)(hp:Knot b U) : Sun b (swamp U f):= by
   obtain he:= sunny h; have hm: Spotty (swamp U f) (fun i=> feeD i • ocean i U (f i)):= ((he.and high0).mono fun i hi=> swamp_spec hp hi.1 hi.2); constructor
   · obtain ⟨R,hR,hx⟩:= Metric.mem_nhds_iff.mp (way.mem_nhds (show (0:ℂ)∈Town by simpa using Town_nat 0)); exact mer.congr (mer.high (h.mer.rode hp ( show (∀ᶠ i in dotty, Sturdy b (f i)) from h.dice)) (fun i hi=> fee_H i (hx hi)) hR) hm.symm
   filter_upwards [hm,he,high0] with i hi hX hv; rw [hi]; exact (torn hv hX hp|>.smul (feeD i)).token
lemma Sun.tree (h: Sun b f)(he:Sun b g)(hx:reverseF U)(hp: Knot b U)(hu:closedF U c): Sun b (tapeB (squad U) f g):= by
    refine ⟨h.mer.trees hp.price he.mer,?_⟩; apply Eventually.mono ((sunny h).and (sunny he)); intro x hx'; change Sturdy b (arbor U (f x) (g x)); exact (Form0.treed hp hu hx hx'.1 hx'.2).token
lemma Sun.Q (h: Sun b f): Sun b (tapeL (fun _=>sweepQ (Wick.Q G)) f):= by
    refine ⟨h.mer.portQ (Wick.Q G) (count_caps G),?_⟩; apply h.dice.mono; intro i hi; change Sturdy b (portZ (Wick.Q G) (f i)); refine zMotion hi ?_; cases b; · exact Cert_all G
    exact Cert0 G
namespace Sun
lemma zero : Sun b (0:Coat G):= ⟨ _root_.YM.MS.Shine.mer.zero,(washed (sturdy b G)).zero⟩
lemma add (h:Sun b f)(hv:Sun b g): Sun b (f+g):= ⟨h.mer.add hv.mer,(washed _).add _ _ h.dice hv.dice⟩
lemma sub (h:Sun b f)(hv:Sun b g): Sun b (f-g):= ⟨h.mer.sub hv.mer, (h.dice.and hv.dice).mono fun _ ht=> (sturdy b G).sub_mem ht.1 ht.2⟩
lemma smul (h:Sun b f)(c:ℂ): Sun b (c • f):= ⟨h.mer.static c,h.dice.mono fun _ ht=> (sturdy _ G).smul_mem _ ht⟩
lemma congr (h:Sun b f)(he:Spotty f g): Sun b g:= ⟨h.mer.congr he, (h.dice.and he).mono fun _ ht=>ht.2 ▸ ht.1⟩
lemma tofalse (h:Sun true f): Sun false f:= ⟨h.mer,(sunny h).mono fun _ hi=> hi.clearer.token⟩
lemma HeapS : Heap (Sun (G:=G) b):= ⟨zero,fun _ _=>add⟩
end Sun
abbrev Moony (b:Bool)(X: Flats G) := SeedP (Sun b) X
namespace Moony
lemma toss (h:Moony true X): Moony false X:=fun i=>(h i).tofalse
lemma toast (h:Moony b X): Merg X:= fun i=> (h i).mer
lemma cycle (h: Moony b F)(he:Knot b U): Moony b (CycleN U F):= Sun.HeapS.pipe _ _ _ (fun i=> swamp_m (h i) he)
lemma tree (h:Moony b X)(he:Moony b F)(hp:Knot b U)(ht:reverseF U)(hu: closedF U c): Moony b (TreeN U X F):= Sun.HeapS.explo _ X F (fun i j=>(h i).tree (he j) ht hp hu)
lemma tap (h:Moony b F): Moony b (QN G F):= Sun.HeapS.pipe _ _ _ (fun i=> (h i).Q)
lemma sunup (h:Moony b F): ∀ᶠ i in dotty,∀ j,Form0 b (F j i):= facade F (fun _ _ F=> Form0 b F) id dotty (fun _ _=> Form0.zero) (fun i=> sunny (h i))
lemma march (h:Moony b F)(t:ℕ): ∀ᶠ i in dotty,∀ y s, Form0 b (Parade F t y s i):= by
    apply (sunup h).mono; intro i hi y s; unfold Parade Finsupp.sum; let U(f:Mob G):= Form0 b f;
    have hu(S:Finset ℕ): Form0 b (∑ j∈ S,hikeP i t j y s (F j i)):= by induction S using Finset.induction with| empty=> simp only [Finset.sum_empty]; exact Form0.zero| insert j q he ih=> rw [Finset.sum_insert he]; exact ( fseed (hi j) (vamp i t j) s|>.smul _).add ih
    exact hu _
end Moony
-- rank
lemma capC (q:ℤ)(h:Cap q F)(hp:Moony b F)(hu:Knot b U): Cap (q-2) ( CycleN U F) := by
   refine (washed (grade (q-2) G)).pipe _ _ _ (fun i=>?_); filter_upwards [sunny (hp i),h i,high0] with s hs ht hu'; rw [swamp_spec hu hs hu']; exact (grade _ G).smul_mem _ (cap_ocean hs hu hu' ht)
lemma capA (h:Cap t F)(hp: Cap q X)(he:reverseF U): Cap (t+q-2) (TreeN U F X):= by
    refine (washed (grade (t+q-2) G)).explo _ F X (fun i j=>?_); exact ((h i).and ( hp j)).mono fun i hu=> whole he hu.1 hu.2
lemma cap_QN (h:Cap t X): Cap t (QN G X):= (washed (grade t G)).pipe _ _ _ (fun i=> (h i).mono fun _ hp=> cap_Q _ hp)
end YM.MS.Train
