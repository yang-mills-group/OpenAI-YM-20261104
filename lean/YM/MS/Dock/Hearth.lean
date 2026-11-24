import YM.MS.Dock.Cream
/-!
# AC Hank -- constructing a Joint. Record spin and capacity
 separately for marks and bulk.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z J L:Flats G}{K U:Mob G}{f g p q:Coat G}{b c:Bool}{t r:ℤ}{n h ℓ:ℕ}{i:ℂ}
-- Bareness estimates need global ℓ eventually
structure Cap0 (b:Bool)(i r:ℤ)(F:Coat G): Prop where
    fine: Fine b i F
    cap: To F (grade r G)
abbrev ClockD (b:Bool)(i r:ℤ)(F:Flats G): Prop:= SeedP (Cap0 (G:=G) b i r) F
namespace Cap0
lemma zero : Cap0 b t r (0:Coat G):= ⟨ Fine.zero,(washed _).zero⟩
lemma add (h:Cap0 b t r f)(he:Cap0 b t r g): Cap0 b t r (f+g):= ⟨h.fine.add he.fine,(washed _).add _ _ h.cap he.cap⟩
lemma sub (h: Cap0 b t r f)(he: Cap0 b t r g): Cap0 b t r (f-g):= ⟨ h.fine.sub he.fine,(h.cap.and he.cap).mono fun _ hi=> (grade r G).sub_mem hi.1 hi.2⟩
lemma smul (h:Cap0 b t r f)(hx:star i=i): Cap0 b t r (i • f):= ⟨ h.fine.smul hx, h.cap.mono fun _ hi=> (grade r G).smul_mem _ hi⟩
lemma neg (h:Cap0 b t r f): Cap0 b t r (-f):= by simpa only [zero_sub] using Cap0.zero.sub h
lemma collects (h:Cap0 b t r f){u:ℤ}(hp:r≤u): Cap0 b t u f:= ⟨h.fine,h.cap.mono fun j hj=> show Issue u (f j) from fun n l hz=> (show Issue r (f j) from hj) n l (hp.trans_lt hz)⟩
lemma alter (h:Cap0 b t r f)(he:Spotty f g): Cap0 b t r g:= ⟨ h.fine.alter he, (h.cap.and he).mono fun _ hi=> hi.2 ▸ hi.1⟩
lemma heap : Heap ( Cap0 (G:=G) b t r):= ⟨ zero,fun _ _=>add⟩
lemma fine_bar (hF:Cap0 b t r f)(ℓ h:ℕ): Cap0 b t r (fun i=> Bless h ℓ i (f i)):= by
   have H:= hF.fine; have hz{Q:LeanC G}(hh:Need Q)(hp: To f Q): To (fun i=> Bless h ℓ i (f i)) Q:= by filter_upwards [hp,H.tune.mer.price,vamp_up h ℓ] with i hi ht hL; exact road Q hh hi ht hL
   refine ⟨ ⟨ ⟨blessed h ℓ H.tune.mer,hz need_true H.tune.dice ⟩, hz need_col H.ghost,?_⟩, hz need_tail hF.cap⟩; unfold realAlong; filter_upwards [(show ∀ᶠ i:ℝ in realDotty, f i ∈ sight G from H.sense), dotty_touch.eventually (H.tune.mer.price), dotty_touch.eventually (vamp_up h ℓ)] with i hi ht hL; exact seen (sight G) need_eye hi ht (by simp) hL
end Cap0
lemma clockCap (h:ClockD b t r J): Cap r J:= fun i=> (h i).cap
lemma clockMoon (h: ClockD b t r J): Moony b J:= fun i => (h i).fine.tune
lemma clockTrans {q:ℤ}(h:ClockD b t r J)(he:r≤q): ClockD b t q J := fun i=> (h i).collects he
lemma clockWind (h:ClockD b t r J)(he:Pact J F): ClockD b t r F:= fun i=>(h i).alter (he i)
lemma mintCap (h:ClockD b t r J)(hp:Rent J ℓ): Cap0 b t r (Mint ℓ J) := ⟨ ⟨⟨⟨_,Mint_cap hp⟩, Eventually.of_forall ( MintC hp _ need_true (fun i=> (h i).fine.tune.dice) )⟩, Eventually.of_forall (MintC hp _ need_col (fun i=> (h i).fine.ghost)), (show realAlong _ _ from Eventually.of_forall (MintR hp _ need_eye (fun i=> (h i).fine.sense)))⟩, Eventually.of_forall (MintC hp _ need_tail (clockCap h))⟩
lemma brightR (z:ℂ)(n ℓ:ℕ): Bless n ℓ z (0:Mob G) =0:= by
    simp only [Bless,cPos,progress,wood,Hem.clear,haze,tad0,Finset.sum_const_zero, sub_zero, ← cert, map_zero]; split_ifs <;> ext <;> simp [mend]

def wheels (F:Flats G)(n:ℕ): Flats G := F.sum fun i f=> Finsupp.single i (fun p=> Bless n i p (f p))
lemma loopy (F:Flats G)(n:ℕ)(i:ℕ): wheels F n i=(fun p=> Bless n i p (F i p)):= by
    rw [wheels, Finsupp.sum_apply, Finsupp.sum]; by_cases he: i∈F.support; · rw [Finset.sum_eq_single i]; simp; intro k hk h; simp [h]; exact fun h=>(h he).elim
    rw [ Finsupp.notMem_support_iff.mp he]; simp_rw [Pi.zero_apply,brightR]; refine Finset.sum_eq_zero fun k hk=> Finsupp.single_eq_of_ne (fun h=>he (h.symm ▸ hk)) -- type ambiguity
lemma scooter (hd:ClockD b t r F) (he:Return F 0 n): Vibe n (wheels F n) F∧ClockD b t r (wheels F n)∧ Return (wheels F n) 0 n:= by
    have hm(ℓ:ℕ):= blessAll (F ℓ) ( hd ℓ).fine.tune.mer (n:=n) (ℓ:=ℓ) (fun hp=> hp.symm ▸ he); refine ⟨ two _ _ (fun i ℓ F H=> Mell.Trail F H (vamp i n ℓ)) id dotty (fun i k=> Mell.Trail.zero) ?_, ?_,?_⟩
    · intro i; rw [loopy]; exact (hm i).mono fun z hz=> hz.1
    · intro i; rw [loopy]; exact (hd i).fine_bar i n
    unfold Return; rw [loopy]; filter_upwards [hm 0] with i hi; simpa only [vampV,Pi.zero_apply] using hi.2 rfl
end YM.MS.Dock
