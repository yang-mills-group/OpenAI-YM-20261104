import YM.MS.Train.Music
/-!
# Commutes regularization mode finite part with operations precisely

Used e.g. close under cycles at this ℓ perturbation order (rank-descending effect). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z:Flats G}{K L E:Mob G}{f g:Coat G}{b c:Bool}{t q:ℤ}{U V:Rip G}{k m n h ℓ:ℕ}{i:ℂ}{s:ℝ}
-- ↑d near.
lemma all0 (hx:Moony b F): Moony false F:= by cases b; exact hx; exact Moony.toss hx
lemma heed (hp:Knot b U): Knot false U:= by cases b; exact hp; exact hp.clearer
lemma tenorLift (y:ℝ)(hp:Knot false U)(hx:∀ᶠ i in dotty,Form0 false (f i))(hv:Lift f K) : Lift (fun i=> unitC i y U (f i)) (unitC 0 y U K):= by
    obtain ⟨R,hR,hT⟩:= fee_T y; have ht: ∀ᶠ i in dotty, Sturdy false (f i):= hx.mono fun i hi=> hi.token
    have he:= Lift.acre hv (P:= Sturdy false) ( Wind.time (b:=false)) ht; have hm:= Lift.high (Lift.cycle hv hp ht) hT hR; rw [unitC,LinearMap.smul_apply,port_spec (show (0:ℂ)∈Town by simpa using Town_nat 0) _ hp (⟨Lift.price hv, he⟩) ]; refine Lift.congr hm ?_; filter_upwards [hx,high0] with i hi hI; simp only [unitC,LinearMap.smul_apply,port_spec hI _ hp hi]; rfl
lemma lift_up (s y:ℝ)(h: Lift (Parade F k y s) K)(hx:Moony b F)(ho:Knot b U){a:ℂ}(hv:a-4=(k:ℂ)-ℓ) : Lift (Parade (CycleN U F) ℓ y s) (unitC 0 y (pulse a s U) K):= by
    have hr:= Moony.march (all0 hx) k; obtain hp:= (tenorLift y (fze (heed ho) a s) (hr.mono fun i hi=> hi y s) h); exact Lift.congr hp (((Moony.sunup (all0 hx)).and high0).mono fun i hi=> Eq.symm (length_at hi.2 (heed ho) hi.1 hv s y))
lemma Cit (h:Stay k F)(hf:Moony b F)(ho:Knot b U){a:ℂ}(hp:a-4=(k:ℂ)-ℓ): Stay ℓ (CycleN U F):= fun y s=> by obtain ⟨F',hV⟩:= h y s; exact ⟨_,lift_up s y hV hf ho hp⟩
lemma lift_root {a:ℂ}(hy:a-(n:ℂ)-m=-(h:ℂ))(hv:Knot b U)(hx:reverseF U)(y s:ℝ)(hp:Lift (Parade F n y s) K)(hX:Lift (Parade X m y s) L) : Lift (Parade (TreeN U F X) h y s) (arbor (pulse a s U) K L):= Lift.congr (Lift.tree hp (priced1 hv.price a s) hX) (Eventually.of_forall fun i=> (tree_at hx hy y s i).symm)
lemma StayB {a:ℂ}(hy:a-(n:ℂ)-m=-(h:ℂ))(hv:Knot b U)(hx:reverseF U)(hp:Stay n F)(ht:Stay m X): Stay h (TreeN U F X):= fun y s=> by obtain ⟨K,hK⟩:=hp y s; obtain ⟨L,hL⟩:=ht y s; exact ⟨_, lift_root hy hv hx _ _ hK hL⟩
lemma Lift_Q (y s:ℝ)(hp:Lift ( Parade F h y s) K): Lift ( Parade (QN G F) (h+1) y s) ( portZ (Q G) K):= Lift.congr (Lift.portQ hp (count_caps G)) (Eventually.of_forall fun i=> (Q_at h s y i).symm)
lemma Stay_Q (h:ℕ)(hp: Stay h F): Stay (h+1) ( QN G F) := fun y t=> by obtain ⟨K,hp⟩:=hp y t; exact ⟨_, Lift_Q y t hp⟩
lemma Stay_add (hp:Stay h F)(ht:Stay h X): Stay h (F+X):= by intro y s; rw [page_add]; exact Live.add (hp ..) (ht ..)
lemma Stay_sub (hp:Stay h F)(ht:Stay h X): Stay h (F-X):= by intro y s; rw [page_sub]; exact Live.sub (hp ..) (ht ..)
lemma hike_mul (m:ℕ)(c:ℂ)(x:ℂ)(y s:ℝ)(h:ℕ)(F:Mob G): hikeP x h m y s (c • F)=c • hikeP x h m y s F:= by unfold hikeP; rw [← cert,map_smul,smul_comm]; rfl
lemma page_smul (c:ℂ)(F:Flats G)(h:ℕ)(y s:ℝ): Parade (c • F) h y s=c • Parade F h y s:= by
    funext i; rw [ Page F.support Finsupp.support_smul]; conv_rhs=> rw [Page F.support (by rfl)]
    simp only [Finset.sum_apply,Finsupp.smul_apply, Pi.smul_apply, Finset.smul_sum,hike_mul]
lemma Stay_scale (h:Stay m F)(c:ℂ): Stay m (c • F):= by intro y s; rw [page_smul]; exact Live.static (h ..) c
lemma viewAll (y:ℝ)(N:ℕ) (Q:LeanC G)(ht: Need Q)(hp: SeedP (fun F=> To F Q) F): ∀ᶠ i in dotty,∀ s, Parade F N y s i ∈Q:= by
    filter_upwards [facade F (fun _ _ x=> x∈Q) id dotty (fun _ _=>Q.zero_mem) hp] with i hi s; unfold Parade Finsupp.sum; exact Q.sum_mem fun j _=> Q.smul_mem _ ( ht.seo (hi j) _ _)
end YM.MS.Train
