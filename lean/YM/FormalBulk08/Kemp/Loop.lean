import YM.FormalBulk08.Kemp.Page

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree Wine
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type} {l i u j t r D d : ℕ}{K: KernelChoices}
variable (a:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(Y X:Anthem D G)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
 (hp: Wade a Y l)(hv: Story W (pink K.penalty P.wing))(hr: LocalRatio ρ)(hL:2≤P.L.val)(ht:4≤t)(hu:l≤u)
 (hz:Wade a X l)(k:(n:Side)→(primary P.patch K n).Choices)

lemma flag_plus [Fintype I][DecidableEq I] (H:Hull I J)(p Z X:Pap (I⊕J)): flag H p (Z+X) = flag H p Z + flag H p X:= by unfold flag; rw [map_add,mul_add]; simp only [map_add,mul_add]
lemma fuel_worm [Fintype I][DecidableEq I](H:Hull I J)(p:Pence): (toInk H) (worm (I⊕J) p)=boost I (worm J p) := by
   unfold worm toInk roam; rw [change_after]; have he:(insertAt ℝ (fueled H)).comp MvPolynomial.C= C.comp (MvPolynomial.C.comp MvPolynomial.C) := RingHom.ext fun c=> by simp
   rw [he,pure_map]; unfold boost; rw [PowerSeries.map_comp]; rfl
lemma flag_earn [Fintype I][DecidableEq I](H:Hull I J)(b W:Pap (I⊕J))(p:Pence): flag H b (worm (I⊕J) p*W)=worm J p * flag H b W := by
   unfold flag; rw [map_mul (toInk H),fuel_worm,mul_left_comm _ (boost I _),suction,mul_left_comm]
lemma seat_ages {c f : Side}(S : StepData c f)(F:Forest S.ratio)(Q:Pap (wire G f))(p:Pence):Reef.seat F (worm _ p *Q)= worm _ p*Reef.seat F Q:= by
    unfold Reef.seat; rw [map_mul,map_mul]; apply congr_arg₂ _ _ rfl
    rw [show PowerSeries.map _ (worm (wire G f) p)= worm (Glob G c f) p from ?_]; exact worm_roam ..
    ext1 n; unfold worm; rw [coeff_map,coeff_map,coeff_map]; exact MvPolynomial.rename_C ..
lemma tossed_pp (n:Side)(p R T:Pap (wire G (n*P.patch.L))) : tossed P ρ h V n (k n) p (R+T) = tossed P ρ h V n (k n) p R + tossed P ρ h V n (k n) p T:= by unfold tossed Reef.seat;rw [map_add,map_add,flag_plus]
lemma tossed_cash (n:Side)(p R:Pap (wire G (n*P.patch.L)))(b:Pence): tossed P ρ h V n (k n) p (worm _ b *R)=worm _ b * tossed P ρ h V n (k n) p R:= by unfold tossed;rw [seat_ages (primary P.patch K n) _ R,flag_earn]

variable {X Y}
include hp hu
lemma preQ (p:Dawn.Studio D)(d n): quickP P V W Y ρ h hL d u p n (k n)= PowerSeries.C (MvPolynomial.C (aven P.L d))*∑ x:Site P.L,tossed P ρ h V n (k n) (stone W _) (resite (wrap _ (lift x)) (banner l (Y (Dawn.throughW x _ hL p)) _)) := by
    unfold quickP; apply congr_arg; refine Finset.sum_congr rfl fun x _=>?_; rw [stepsong, seated _ _ _ _ ((hp.through hu).1 _) (hp.2.1 _), banner_rise hp hu]
omit hu hp in
lemma resite_cash {p:Side}(U:Pap (wire G p))(t:Site p)(b:Pence): resite t (worm _ b*U)=worm _ b*resite t U:= by unfold resite; rw [map_mul]; rw [show PowerSeries.map _ (worm (wire G p) b)=worm (wire G p) b from ?_];ext1 n; rw [coeff_map,worm,coeff_map]; exact MvPolynomial.rename_C ..
lemma PactQ (p:Dawn.Studio D)(d n)(b:Pence):quickP P V W (launch b Y) ρ h hL d u p n (k n)= worm _ b*quickP P V W Y ρ h hL d u p n (k n):= by
    rw [preQ a P V W _ h (hp.launch b) hL hu, preQ a P V W _ h hp hL hu,mul_left_comm]; apply congr_arg; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [banner_mul hp _ b _, resite_cash, tossed_cash]
include hz
lemma plusQ (p:Dawn.Studio D)(d n):quickP P V W (Y+X) ρ h hL d u p n (k n)=quickP P V W Y ρ h hL d u p n (k n)+ quickP P V W X ρ h hL d u p n (k n):=by
    simp_rw [preQ a P V W _ h hp hL hu,preQ a P V W _ h hz hL hu]; rw [preQ a P V W _ h (hp.add hz) hL hu, ←mul_add,←Finset.sum_add_distrib]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_; rw [Pi.add_apply,banner_add _ _ _ _ (hp.summable _) (hz.summable _),resite,map_add,tossed_pp];rfl

omit hu hz hp
lemma rancho_launch {n:Side}(b:Pence)(P: Pap (wire G n))(e r:ℕ): rancho (worm _ b*P) e r=∑ i∈Finset.antidiagonal e, coeff i.1 b • rancho P i.2 r := by -- auto n
    unfold rancho; rw [coeff_mul,←canyon_eq,map_sum]; refine Finset.sum_congr rfl fun x _=> ?_; rw [worm,coeff_map,←MvPolynomial.smul_eq_C_mul,map_smul];rfl
include hp hv hr ht hu
lemma quick_pact (p:Dawn.Studio D)(d : ℕ)(b:Pence):quick P V W (launch b Y) ρ h hL d u p= launch b (quick P V W Y ρ h hL d u) p:= by
    let T:= quick P V W Y ρ h hL d u p; let k:(n:Side)→(primary P.patch K n).Choices:=fun n=> Classical.choice (chooseable n _ (primary P.patch K n))
    let U n:= quickP P V W Y ρ h hL d u p n (k n)
    funext e r v; obtain ⟨s,hs,H,-⟩:=brig a P V (launch b Y) W _ h (hp.launch b) hv hr hL ht hu k e r d
    refine tendsto_nhds_unique ((H p).1 v) ?_
    have he e : Light (T e r) (fun n=>rancho (U n) e r):= ((brig a P V Y W _ h hp hv hr hL ht hu k e r d).choose_spec.2.1 p).1
    change Tendsto _ _ (𝓝 ((surf b T e r) v)); unfold surf;rw [Finset.sum_apply]; apply (tendsto_finsetSum _ (fun i _=>(he i.2 v).const_mul (coeff i.1 b))).congr'
    exact .of_forall fun n=>by simp only; rw [PactQ a P V W _ h hp hL hu,rancho_launch, Finset.sum_apply];rfl
include hz
lemma quick_pair (p:Dawn.Studio D)(d:ℕ): quick P V W (Y+X) ρ h hL d u p = quick P V W Y ρ h hL d u p + quick P V W X ρ h hL d u p:= by
    let Q n:= Classical.choice (chooseable n _ (primary P.patch K n))
    funext e r v; obtain ⟨s,-,H,-⟩:=brig a P V (Y+X) W _ h (hp.add hz) hv hr hL ht hu Q e r d
    obtain ⟨w,-,HS,-⟩:=brig a P V Y W _ h hp hv hr hL ht hu Q e r d
    obtain ⟨w,-,HV,-⟩:=brig a P V X W _ h hz hv hr hL ht hu Q e r d
    refine tendsto_nhds_unique ((H p).1 v) ((((HS p).1 v).add ((HV p).1 v)).congr' (.of_forall (fun n=>?_))) ; dsimp only;rw [plusQ a P V W _ h hp hL hu hz]; simp only [rancho,map_add,marble_add];rfl
end YM.FormalBulk08.Kemp
