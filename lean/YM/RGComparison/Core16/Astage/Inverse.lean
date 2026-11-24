import YM.RGComparison.Core16.Astage.Panel
/-!
# Resolve the inverse bootstrapping issue

A consumer taking two-point diagnostic pairs on the same *physical fields*, **prior to**
using a Reader/OPE matching statement at positive output horizon. Clearances from `Panel`.
Use the reflected condition on the A pivots from formal-side normalizations, with leading
comparison required only from the horizon-zero report machinery. Deduce the quantitative
bounds on the ACTUAL readout matrices; no `MatrixTicket` needed. Pay same-horizon meter-to-ref
cost of exponential engineering power by squaring and using actual global estimates (important
when the meter mixes many weights!).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Panel
open Filter Function Real Metric Set MeasureTheory OPE
open Table Orbits Word Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι:Type}{l:Filter ι}
section linear
variable {V W V':Type*}[NormedAddCommGroup V][NormedSpace ℂ V]
    [NormedAddCommGroup W][NormedSpace ℂ W]
    [NormedAddCommGroup V'][NormedSpace ℂ V']

-- Lift report and cross-Gram on common synthetic & physical spaces incl all letters.
-- We account for column conjugacy/reflection visibly via `reflect`. Thus the inversion against
-- all second columns computes same solution as after inserting reflection/conjugating them.
def address (A:V→L[ℂ] W)(p:W→L[ℂ] W→L[ℂ] ℂ) : W→L[ℂ] (V→L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ V W ℂ |>.flip A).comp p
lemma address_apply (A:V→L[ℂ] W)(p:W→L[ℂ] W→L[ℂ] ℂ) (x y): address A p x y=p x (A y):=rfl

variable [FiniteDimensional ℂ V][FiniteDimensional ℂ W]
-- keep numerical continuation even if on early regulators with singular solve.
-- For Gram read use only after proving bijectivity.
def solve (A:V→L[ℂ] W) : W→L[ℂ] V:=
    if h: Bijective A then LinearMap.toContinuousLinearMap ((LinearEquiv.ofBijective A.toLinearMap h).symm.toLinearMap) else 0
omit [FiniteDimensional ℂ V] in
lemma solves {A:V→L[ℂ] W} (h:Bijective A) (x:W) (y:V) : solve A (A y)=y ∧ A (solve A x)=x:=by
    let S:=LinearEquiv.ofBijective A.toLinearMap h; rw [solve,dif_pos h]; exact ⟨S.symm_apply_apply y,S.apply_symm_apply x⟩

variable {A:ι→ V→L[ℂ]V→L[ℂ]ℂ}{r:V→V}
omit [FiniteDimensional ℂ V] in
lemma coin {k b:ℝ}(hk:0 ≤ k)(hρ:∀ v, ‖r v‖ ≤ b*‖v‖) (j:ι)
   (h:∀ v, ‖v‖^2 ≤ k*‖A j v (r v)‖): ∀ v, ‖v‖ ≤ k*b*‖A j v‖:=by
    intro v; rcases eq_or_ne v 0 with rfl|hv; · simp
    let u:= A j v; have hh:= norm_pos_iff.mpr hv; have he :‖v‖*‖v‖ ≤ k*b*‖u‖*‖v‖:= (sq ‖v‖) ▸ ((h v).trans ((mul_le_mul_of_nonneg_left (((A j v).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hρ v) (norm_nonneg _))) hk).trans_eq (by unfold u; ring))) -- check orientation
    exact le_of_mul_le_mul_right he hh

variable {a:ι→V→L[ℂ] V→L[ℂ] ℂ}
omit [FiniteDimensional ℂ V] in
lemma transplant {Λ:ι→ℝ}{c b:ℝ}(h:Tendsto Λ l atTop)
    (hr:∀ z, ‖r z‖ ≤ c*‖z‖)(p:ℕ)(hv:∀ᶠ i in l, ∀ x, ‖x‖^2 ≤ (Λ i)^p*‖a i x (r x)‖)
    (he: RateLE l Λ (fun i=> a i - A i) b)(hb:b<0):
    ∃ q:ℕ, ∀ᶠ i in l, ∀ x, ‖x‖^2 ≤ (Λ i)^q*‖A i x (r x)‖:=by
    have ht:= ((Wallet.id h).pow h p|>.subpower h).mul (show RateLE l Λ (fun i=> ‖a i-A i‖) b from he.transfer (Eventually.of_forall (fun i=> (Real.norm_of_nonneg (norm_nonneg (a i-A i))).le)))|>.mul (RateLE.const c h)
    have hϑ : RateLE l Λ (fun i=>Λ i^p * ‖a i-A i‖ * c) b:= by simpa only [zero_add,add_zero] using ht
    refine ⟨p+1,?_⟩; filter_upwards [hv,(hϑ.tends hb h).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)), h.eventually_ge_atTop 2] with i hi hz hh
    intro x; let L:= r x; let x' := a i; let y:= A i
    let f:=Λ i^p; have hf:0 ≤ f:= pow_nonneg (zero_le_two.trans hh) _
    have hr':=(hr x); have hx: ‖A i x L - a i x L‖ ≤ ‖a i-A i‖ * ‖x‖ * (c*‖x‖):= calc
       _ = ‖(a i-A i) x L‖:= norm_sub_rev ..
       _ ≤ _:= ((ContinuousLinearMap.le_opNorm _ L)).trans (mul_le_mul ((a i-A i).le_opNorm _) hr' (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) -- nested trick
    have hu':f * (‖a i-A i‖* ‖x‖*(c*‖x‖)) ≤ 1/2 * ‖x‖^2:=by
       calc _ = (Λ i^p * ‖a i-A i‖ * c) * ‖x‖^2 := by unfold f; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hz (sq_nonneg ‖x‖)
    have hu:‖x‖^2 ≤ f*‖y x L‖ + 1/2*‖x‖^2:=by
       have hs: ‖x' x L‖ ≤ ‖y x L‖+ ‖A i x L-a i x L‖:= by linarith only [norm_sub_norm_le (x' x L) (y x L),norm_sub_rev (A i x L) (a i x L)]
       apply (hi x).trans
       apply (mul_le_mul_of_nonneg_left (hs.trans (add_le_add le_rfl hx)) hf).trans
       rw [mul_add]; exact add_le_add le_rfl hu'
    apply le_trans (show _ ≤ (f*2)*‖A i x L‖ from by linarith only [hu]) ?_; rw [pow_succ]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hf) (norm_nonneg _)
lemma enabled {k b:ℝ}{p: ι → W→L[ℂ] W→L[ℂ] ℂ}{T:ι→V→L[ℂ] W}(hr:Module.finrank ℂ V=Module.finrank ℂ W)
   (hk:0≤k)(hρ:∀ v, ‖r v‖ ≤ b*‖v‖) (j:ι)
   (h:∀ v:V, ‖v‖^2 ≤ k*‖p j (T j v) (T j (r v))‖):
      let G:= (address (T j) (p j)).comp (T j)
      Bijective (T j) ∧ Bijective G ∧ ∀ u v, ‖v‖ ≤ k*b*‖G v‖ ∧ ‖solve G u‖ ≤ k*b*‖u‖:=by
    intro G
    have hh:= coin (A:=fun (_:ι)=>G) hk hρ j h
    have he:Injective G:= LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot' (f:=G.toLinearMap)).mpr (fun v hv=>norm_le_zero_iff.mp ((hh v).trans (by rw [show G v=0 from hv]; simp))))
    have ht' : Module.finrank ℂ V=Module.finrank ℂ (V→L[ℂ] ℂ):= by
       rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap : (V→ₗ[ℂ] ℂ) ≃ₗ[ℂ] (V→L[ℂ] ℂ)),Module.finrank_linearMap_self]
    have hf:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=G.toLinearMap) ht'|>.mp he)
    have hi:Injective (T j):= fun u v e => he (DFunLike.congr_arg (address (T j) (p j)) e)
    refine ⟨⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=(T j).toLinearMap) hr).mp hi⟩,⟨he,hf⟩, fun u v=> ⟨hh v,?_⟩⟩
    have hh:=hh (solve G u); rwa [show G _=u from (solves ⟨he,hf⟩ u v).2] at hh
end linear

variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
    (T:Spec.Final C F S) (d:ℕ)
local notation "Q"=> S.Field d
set_option quotPrecheck false
local notation "V"=>(Maxwell.freeTable C.labels).Field d

lemma prices : ∃ b:ℝ,0 ≤ b ∧ (∀ x:V, ‖Levy.reflect (C:=C) d x‖ ≤ b*‖x‖) ∧ ∀ x:Q, ‖Levy.bar T d x‖ ≤ b*‖x‖:=by
    let E(k:Register G)(m:Table k)(t:m.RealSpin):m.Field d→ₗ[ℝ] m.Field d := {
       toFun x:= m.mirror t d (Signed.mirror timeAxis) (m.conj t d x)
       map_add' x y:=by rw [map_add,map_add]
       map_smul' r v:=by
          change m.mirror _ _ _ (m.conj _ _ (r • v)) = r • m.mirror _ _ _ _
          rw [← Complex.coe_smul,←Complex.coe_smul, LinearMap.map_smulₛₗ]; simp }
    let B:= LinearMap.toContinuousLinearMap (E _ (Maxwell.freeTable C.labels) (Maxwell.Free.spin_free C.labels)); let A:=LinearMap.toContinuousLinearMap (E _ S T.room.kernel.spin)
    exact ⟨_, le_trans (norm_nonneg B) (le_max_left ‖B‖ ‖A‖),fun x=>(B.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg x)), fun x => (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg x))⟩
-- Main spatial price, after deriving `actual` *same-horizon* lower-Gram from proposed formal &
-- horizon zero. Use `Enabled` to extract hur from inverse-gram purchase. Estimate from
-- That Physical certificate solves for exact reflection (before character selection).
variable {m:ι→ℕ}{p:ι→ ℝ}
set_option quotPrecheck false
local notation "s"=>ruler C m
local notation "Λ"=>budgetLog C m
set_option maxHeartbeats 920000 in
lemma to_reference {J:Type} [NormedAddCommGroup J][NormedSpace ℂ J]{barPost:J→J} {H:ι→J→L[ℂ] S.Field d}
   (hp:Tendsto m l atTop) {P:ι→(S.Field d→L[ℂ]S.Field d→L[ℂ]ℂ)}(hρ:∀ᶠ i in l, ∀ v, H i (barPost v)= Levy.bar T d (H i v))
   (h:RateLE l s P (d+d:ℝ)) (hu:RateLE l s p 0)
   (he:∀ᶠ i in l, Bijective (H i) ∧ 0 ≤ p i ∧ ∀ v:J, ‖v‖^2 ≤ p i*‖P i (H i v) (H i (barPost v))‖) :
      RateLE l s (fun i=>solve (H i)) (d:ℝ):=by
    have ht:= large_s C hp
    refine lift_price _ ht fun x=>?_
    intro k hk
    let y:=Levy.bar T d x
    have Ht:= ((hu.mul (show RateLE l s (fun i=>‖P i‖) (d+d:ℝ) from h.transfer (Eventually.of_forall (fun i=> (Real.norm_of_nonneg (norm_nonneg (P i))).le)))).mul (RateLE.const (‖x‖*‖y‖) ht)); rw [zero_add,add_zero] at Ht
    filter_upwards [Ht (k+k) (by linarith),he,hρ] with i hi hφ hf
    let f:= H i; let a:= solve f x; let G':= P i
    have hW: (P i (f a) (f (barPost a)))=P i x y:=by rw [show f (barPost a)= Levy.bar T d (f a) from hf _,show f a=x from (solves hφ.1 x a).2]
    have hz:= hφ.2.2 a; rw [show P i _ _=P i x y from hW] at hz
    have he': ‖a‖^2 ≤ (exp (k*s i))^2:= calc
       _ ≤ p i*‖P i x y‖:= hz
       _ ≤ p i*(‖P i‖ * ‖x‖* ‖y‖):= mul_le_mul_of_nonneg_left (((P i x).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((P i).le_opNorm _) (norm_nonneg _))) hφ.2.1
       _ ≤ _:=by refine le_trans (le_of_eq (?_:_=p i*‖P i‖ * (‖x‖*‖y‖))) ((Real.le_norm_self _).trans (hi.trans_eq ?_)); ring; rw [pow_two, ←exp_add, add_mul]
    exact le_of_sq_le_sq he' (exp_pos _|>.le)
end YM.RGComparison.Core16.Astage.Panel
