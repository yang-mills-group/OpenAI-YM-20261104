import YM.SchemeRG11.Flock.Voice
import YM.SchemeRG11.Wilson.Cold
/-! One-edge collapse at anchored mark, pure kinetic in lattice Feynman gauge. Color-orthonormal units. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.North
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical
variable {G:Gauge}
lemma intake_g (x:Cover)(i j:Axis)(A:Bevy G.Color):First.curlAt x i j (linkup A)=bend A i j x:=by
 rw [←curled]; unfold First.curlAt First.linearSq First.Vleft First.Xleft First.Vright First.Xright wideCurl; abel
def radius (p:Shaft G):Touch G:= -∑ i:Axis,(intake p.1.1 i p.1.2 p.2-intake (p.1.1-step i) i p.1.2 p.2)
lemma lineRad (p:Shaft G)(A:Bevy G.Color):sense (cant (linkup A)) (radius p)=(-(lap (A p.1.2))+soar p.1.2 (Flock.dive A)) p.1.1 p.2:=by
 rw [radius,map_neg,map_sum]; simp only [map_sub,speak,intake_g]; rw [show -(lap _)+_ = -(∑ i:Axis,rear i (bend A i p.1.2)) from by rw [pitch]; abel];simp only [Finset.sum_apply,PiLp.sub_apply,Pi.neg_apply,PiLp.neg_apply,WithLp.ofLp_sum,rear_apply]
lemma radius_null{m:ℕ}(p:Shaft G)(A:Bevy G.Color)(h:A∈team G.Color m): sense (cant (linkup A)) (radius p)=0:=by rw [lineRad, show lap (A p.1.2)=0 from h.2.2 _,show Flock.dive A=0 from h.2.1,map_zero]; simp
abbrev Φ := Cellular.coverLine
def flick (x:Cover):Plane ℝ:= fun z=> Φ (z-x)
def beat (p:Shaft G):Bevy ℝ:=fun i=>if i=p.1.2 then flick p.1.1 else 0
lemma lap_p (q x:Cover):lap (flick q) x= -(if x=q then 1 else 0):=by
 rw [lap,LinearMap.sum_apply,Finset.sum_apply,show (if x=q then (1:ℝ) else 0)=(if x-q=0 then 1 else 0) from by by_cases H:x=q<;>simp [H,sub_eq_zero],←Catch.harmonic_kernel]; apply Finset.sum_congr rfl; intro i _; change rear i (soar i _) x=_; rw [rear_apply, soar_apply,soar_apply]; unfold flick Φ; rw [sub_add_cancel]; rw [add_sub_right_comm, sub_right_comm]; ring
lemma sense_single(q:Shaft G): (land G).windfall (Finsupp.single q 1)=cant (linkup (plumage (beat q) (unitColor G q.2))):=by
 rw [Haze.Dose.single_wind]; funext p; unfold land cant; change (if _ then _ else 0)=(beat q p.1.2 p.1.1 • (unitColor G q.2)) p.2
 change _= beat q p.1.2 p.1.1 * (unitColor _ q.2 p.2)
 rw [unitPaint]; unfold beat; by_cases h:q.2=p.2 <;> by_cases e:q.1.2=p.1.2
 · simp only [h,e,and_self, eq_self,↓reduceIte,mul_one]; unfold flick Φ; rw [← neg_sub p.1.1,Catch.nod] -- linter
 all_goals simp [h,e,Ne.symm]
-- compute grade term at p for convolution lambda
lemma leap_gamma (x j y)(k:Axis): soar j (rear k (flick y)) x= -(soar k (fun z=> soar j (flick z) x) y):=by
 rw [soar_rear]; simp only [rear_apply,soar_apply,flick]; rw [← sub_sub,← sub_sub,show x-step k+step j=x+step j-step k by abel,sub_right_comm x (step k) y,sub_right_comm (x+step j) (step k) y]; abel
lemma dive_wave(q:Shaft G): Flock.dive (beat q)=rear q.1.2 (flick q.1.1):=by rw [dive_apply]; unfold beat; exact Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun i _ hi=>by rw [if_neg hi,map_zero]) |>.trans (by rw [if_pos rfl]) -- check
abbrev knob(p:Shaft G):Plane G.Color:= fun z=> -(soar p.1.2 (flick z) p.1.1) • unitColor G p.2
abbrev splinter(p:Shaft G):Shaft G→ℝ:= Pi.single p 1
lemma arith (p q:Shaft G)(H:Cover→ℝ):(-(lap (beat q p.1.2) p.1.1 • unitColor G q.2)+(-(H (q.1.1+step q.1.2)-H q.1.1) • unitColor G q.2)) p.2= splinter p q + (-H (q.1.1+step q.1.2) • unitColor G p.2 - -H q.1.1 • unitColor G p.2) q.2:=by
 unfold beat splinter; rw [Pi.single_apply]; simp only [PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,unitPaint,PiLp.sub_apply]
 rcases p with ⟨⟨x,i⟩,a⟩; rcases q with ⟨⟨y,j⟩,b⟩
 simp only [Prod.mk.injEq]; by_cases h:a=b
 · subst b; by_cases e:i=j
   · subst j; rw [if_pos rfl,lap_p]; by_cases e:x=y<;> simp [e,Ne.symm] <;> ring
   rw [if_neg e,map_zero]; simp [e,Ne.symm]; ring
 simp [h,Ne.symm]
lemma arith_b(p q:Shaft G):sense (cant (linkup (plumage (beat q) (unitColor G q.2)))) (radius p)= splinter p q+cant (ascent (knob p)) q:=by
 let f:=beat q; let U:=plumage f (unitColor G q.2); let C:ℝ→ₗ[ℝ] G.Color:=(LinearMap.id:Module.End ℝ ℝ).smulRight (unitColor G q.2)
 have he(i:Axis): U i=C ∘ f i:=rfl
 change sense (cant (linkup U)) _=_; rw [lineRad,show Flock.dive U=C ∘ Flock.dive f from dive_linear C f, he, lap_linear, soaring_map,Pi.add_apply,Pi.neg_apply,comp_apply,comp_apply,dive_wave]
 simp only [leap_gamma]
 let H(y:Cover):= soar p.1.2 (flick y) p.1.1
 exact arith p q H
lemma domino(p:Shaft G): (land G).windfall (radius p)=splinter p+cant (ascent (knob p)):=by
 funext q; let f:=beat q; let U:=plumage f (unitColor G q.2); let C:ℝ→ₗ[ℝ] G.Color:=(LinearMap.id:Module.End ℝ ℝ).smulRight (unitColor G q.2)
 have hh: (land G).windfall (radius p) q=sense (cant (linkup U)) (radius p):=by
   rw [show cant (linkup U)=_ from (sense_single q).symm]; have H: sense ((land G).windfall (radius p)) (Finsupp.single q 1)=sense ((land G).windfall (Finsupp.single q 1)) (radius p) := (land G).bed_comm _ _ 
   simp only [sense,Finsupp.linearCombination_single,one_smul] at H; exact H
 exact hh.trans (arith_b p q)
lemma final_d (p:Shaft G)(q:vellum G)(h:∀ e,vent (cant (ascent e)) q=0): vent ((land G).windfall (radius p)) q=vent (splinter p) q:=by rw [domino,vent_add,h,add_zero]
end YM.SchemeRG11.North
