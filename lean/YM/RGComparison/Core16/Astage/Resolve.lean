import YM.RGComparison.Core16.Astage.Tape

/-!
# qpta Gram/report conversion closes without the later logarithmic-price ticket

Two independent error grades come in from the q-comparison: *spatial* error landing in
true physical Field coordinates, and the local accuracy after closure/soft window landing on full
native coupling-cost coordinates. ***Keep them separate.*** The former survives the potentially
huge continuation to measuring frames & the latter need not. Use the latter only on full
vectors/Grams out of the calculation *without inverses to the fixed physical basis*. Then prove
the sharp report error in the filtration pivot measuring frame (input pivots through their own
horizons are kept in the actual and A couplings throughout these hypotheses; this conversion is
on the entire output horizon). This shows no circular use of MATCHING in predicting the inverse
estimates sufficient for the last bootstrap on supplying these reports. All positive-coupling
estimates referenced in this file are still consume-side, not claiming the physical closure or
the *lower precision* Gram entries. In particular don't replace income hypotheses with an assumed
small perturbation of the sharp readout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Panel
open Filter Function Real Metric Set MeasureTheory OPE
open Table Orbits Word Asymptotics Tape
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι:Type}{l:Filter ι}
variable {G:Gauge}{C:Family G}{hG:G.Simple}{S:Table C.book}{F:Extraction.Order}
    (T:Spec.Final C F S) (d:ℕ)
set_option quotPrecheck false
local notation "Q"=> S.Field d
local notation "Λ"=>budgetLog C
local notation "s"=> ruler C

section bridge
variable {V W V':Type}[NormedAddCommGroup V][NormedSpace ℂ V]
    [NormedAddCommGroup W][NormedSpace ℂ W]
    [NormedAddCommGroup V'][NormedSpace ℂ V']
-- Note: reader matrices act on full coupling coordinates, not only native quotient.
variable {g χ: ι→ℝ} {A:ι→ V→L[ℂ] V'}{a:ℕ→ι→V→L[ℂ]V'} {B:ι→ W→L[ℂ]V'}
    {b:ℕ→ι→W→L[ℂ] V'} {Y:ι→W}{y:ℕ→ι→ W} {Z:ι→V}{z:ℕ→ι→ V} {R:ℕ}{x:ℝ}
    (hΛ:Tendsto χ l atTop)(hg:RateIs l χ g (-(1/2:ℝ)))(hx:x ≤ 0)
    (hR:-((R:ℝ)+1)/2 ≤ x)
    (hA:Attached l χ g A a R x)(hB:Attached l χ g B b R x)
    (hY:Attached l χ g Y y R x)(hfA:Fits l χ a R)(hfB:Fits l χ b R)(hf:Fits l χ y R)(hZ:Fits l χ z R)

include hg hΛ hx hR hA hB hY hfA hfB hf hZ
lemma refund (he:∀ᶠ i in l,A i (Z i)= B i (Y i))
   (h:∀ k ≤ R, ∀ᶠ i in l, action a z k i = action b y k i)
   {u:ι→ℝ}(hp: ∀ᶠ i in l, ∀ v:V, ‖v‖ ≤ u i * ‖A i v‖)(hh:RateLE l χ u 0) : Attached l χ g Z z R x:=by
    let X:= partialSum g R z
    have h0:Attached l χ g X z R x:= fun r hr=> Eventually.of_forall fun i=> by unfold X; simp [exp_nonneg]
    have h1:=apply_advance hΛ hg hY hB hfB hf hR hx
    have h2:=apply_advance hΛ hg h0 hA hfA hZ hR hx
    have hG:RateLE l χ (fun i=>A i (Z i-X i)) x:=by
       apply (RateLE.sub h1 h2 hΛ).congr
       have hh':∀ᶠ i in l,(∀ k:Fin (R+1),action a z k.val i=action b y k.val i):=eventually_all.mpr fun k=>h k.val (Nat.le_of_lt_succ k.isLt)
       filter_upwards [he, hh'] with i hi ht; rw [show A i (Z i-X i)= B i (Y i)-A i (X i) by rw [map_sub,hi], show partialSum g R (action a z) i=partialSum g R (action b y) i from Finset.sum_congr rfl (fun k hk=> congr_arg _ (ht ⟨k,Finset.mem_range.mp hk⟩))]; abel
    unfold Attached
    simpa only [zero_add] using hH hp hh hG
where hH (hp:∀ᶠ i in l, ∀ v:V, ‖v‖ ≤ u i * ‖A i v‖)(hu:RateLE l χ u 0) (h:RateLE l χ (fun i=> A i (Z i-partialSum g R z i)) x): RateLE l χ (fun i=>Z i-partialSum g R z i) (0+x):=
       hu.bil h (hp.mono (fun i hf=>(hf (Z i-partialSum g R z i)).trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _))))

-- Upgrade conversion exercised explicitly below: after output frame pivot inverse & division,
-- transform h-spatial etc. Include source lifting which may cost exp(spacing); alignment only.
variable {m:ι→ℕ} (ht:Tendsto m l atTop)
omit hg hΛ hx hR hA hB hY hfA hfB hf hZ
-- translate if needed from any interior billboard. Producers can choose H gains different;
-- only once they're accumulated use the Α hypotheses below.
include ht
omit [NormedSpace ℂ V] in
lemma flat_ignores (hG:G.Simple) (Y:ι→V){x:ℝ}(he:x<0)(h:RateLE l (s m) Y x) (z:ℝ) : RateLE l (Λ m) Y z:=by
    intro q hq; obtain ⟨u,hu,hv⟩:=exists_between he
    have hf:= (negligible C hG ht).const_mul q; rw [mul_zero] at hf
    filter_upwards [(large_s C ht).eventually_gt_atTop 0,h u hu,hf.eventually (le_mem_nhds hv)] with i hi hk he; apply hk.trans (Real.exp_monotone _); exact (le_div_iff₀ hi).1 (by rw [mul_div_assoc]; exact he) -- already ≤ not <

lemma cheap (hG:G.Simple) : RateLE l (s m) (Λ m) 0:=by
    have h:= ((Wallet.clock (large_s C ht)).pays (large_s C ht)); apply h.of_norm_le
    filter_upwards [(negligible C hG ht).eventually (ge_mem_nhds zero_lt_one), (large_Λ C hG ht).eventually_ge_atTop 0,(large_s C ht).eventually_gt_atTop 0] with i hi he hp; rw [Real.norm_of_nonneg he]; exact (div_le_one hp).1 hi
end bridge


section algebra
variable {P D E:Type}[NormedAddCommGroup P][NormedAddCommGroup D][NormedAddCommGroup E]
    [NormedSpace ℂ P][NormedSpace ℂ D][NormedSpace ℂ E]
    [FiniteDimensional ℂ P][FiniteDimensional ℂ D]
    {R r:ℕ}{ξ σ b:ℝ}

lemma revision {A:ι→ P→L[ℂ] D}{F0:ι→ D→L[ℂ] (D→L[ℂ]ℂ)} (rM:P→P) (hrank: Module.finrank ℂ P=Module.finrank ℂ D)
     (hb':∀ x:P, ‖rM x‖≤ b*‖x‖) {K g Z0:ι→ ℝ}(hΓ:Tendsto K l atTop)(hi₀:RateIs l K g (-(1/2:ℝ)))(ht':Tendsto Z0 l atTop)(hτ:RateLE l Z0 K 0)
     (loss:∀ x:ι→ P, ∀ a:ℝ, a<0→ RateLE l Z0 x a → RateLE l K x ξ)
     (lift:∀ v:ι→ℝ, RateLE l Z0 v 0 → (∀ᶠ i in l, Bijective (A i) ∧ 0 ≤ v i ∧ ∀ z:P, ‖z‖^2 ≤ v i*‖F0 i (A i z) (A i (rM z))‖) → RateLE l Z0 (fun i=>solve (A i)) (d:ℝ))
     {Aformal:ℕ→ι→ P→L[ℂ](P→L[ℂ]ℂ)}{Bformal:ℕ→ι→ E→L[ℂ](P→L[ℂ]ℂ)}{c:ι→D}{Y:ι→E}{U:ι→E→L[ℂ]D}{y:ℕ→ι→E}{z:ℕ→ι→P}
    (hx: Attached l K g (fun i=>(address (A i) (F0 i)).comp (A i)) Aformal R ξ)
    (hA: Fits l K Aformal R)(hP:∃ q:ℕ, ∀ᶠ i in l, ∀ v:P, ‖v‖^2 ≤ K i^q * ‖Aformal 0 i v (rM v)‖)
    (hB:Attached l K g (fun i=>(address (A i) (F0 i)).comp (U i)) Bformal R ξ)(he: Fits l K Bformal R)
    (hi: Attached l K g Y y R ξ)(hu: Fits l K y R)
    (hr: Fits l K z R)(hvp:∀ k ≤ R, ∀ᶠ i in l, action Aformal z k i=action Bformal y k i)
    (hc: RateLE l Z0 (fun i=> c i-U i (Y i)) (-(d:ℝ)-σ))
    (hσ:0<σ)(hx1:ξ < -((r:ℝ)+1)/2)(hq:-((R:ℝ)+1)/2 ≤ ξ)(hle:r≤R)
    :
    (∀ᶠ i in l, Bijective (A i)) ∧ ∃ q:ℕ, ∀ᶠ i in l,
       ‖solve (A i) (c i)-partialSum g r z i‖ ≤ g i^(r+1)* K i^q:=by
    -- retain provenance of all factors
    let M : ι→ D→L[ℂ] (D→L[ℂ]ℂ):= F0; let X:=fun i=>(address (A i) (M i)).comp (A i); let Y' i:=(address (A i) (M i)).comp (U i)
    let c' i:= solve (A i) (c i); let Y0 i:= solve (A i) (U i (Y i)); let a':=Aformal 0
    obtain ⟨q,hp⟩:= hP
    let x:ℝ:= (-(1/2:ℝ)); have he₀:= Tape.strict_zero hΓ hi₀ hA
    have hl: ξ ≤ x:=hx1.le.trans (by unfold x; linarith only [Nat.cast_nonneg (α:=ℝ) r])
    let χ i:=X i-partialSum g R Aformal i; let v i:=partialSum g R Aformal i-a' i
    have A0 : RateLE l K χ x:= fun k hk=> hx k (lt_of_le_of_lt hl hk)
    have hhi : RateLE l K (fun i=>χ i+v i) x:= RateLE.add (F:=χ) (F':=v) A0 he₀ hΓ
    have hhi : RateLE l K (fun i=> -(χ i+v i)) x:= RateLE.neg (F:=fun i=>χ i+v i) hhi
    have hα:RateLE l K (fun i=>a' i-X i) x:=(RateLE.congr (F:=fun i=> -(χ i+v i)) hhi (Eventually.of_forall fun i=> by change -((X i - partialSum g R Aformal i) + (partialSum g R Aformal i - a' i)) = a' i - X i; abel))
    obtain ⟨q',hh⟩:= transplant (A:=X) hΓ hb' q hp hα (by unfold x; norm_num)
    let cost i:= K i^q'
    have h0 :∀ᶠ i in l,0≤ cost i:= (hΓ.eventually_ge_atTop 0).mono fun i hi=> pow_nonneg hi _
    have hJ i (hf:0≤cost i)(hz:∀ v, ‖v‖^2 ≤ cost i * ‖X i v (rM v)‖) := enabled (T:=A) (p:=M) hrank hf hb' i hz
    have hβ:∀ᶠ i in l,Bijective (A i):= (h0.and hh).mono fun i ht=> (hJ i ht.1 ht.2).1
    refine ⟨hβ,exactPrecision hΓ hi₀ ?_ hx1 hr hle⟩
    have hY : Attached l K g Y0 z R ξ:=by
       let v i:=cost i*b; apply refund (u:=v) hΓ hi₀ (hl.trans (by unfold x; norm_num)) hq hx hB hi hA he hu hr _ hvp
       · filter_upwards [hh,h0] with i hh h0; exact fun z=>(hJ i h0 hh).2.2 0 z|>.1
       · exact ((Wallet.id hΓ|>.pow hΓ q'|>.mul (Wallet.const hΓ b)).subpower hΓ)
       filter_upwards [hβ] with i hi; change address (A i) (M i) (A i (Y0 i))=_; exact DFunLike.congr_arg (address (A i) (M i)) ((solves hi (U i (Y i)) 0).2)
    let f i:= solve (A i)
    have hv:RateLE l Z0 f (d:ℝ):= lift (fun i=> K i^q') (((hτ.pow q' ht').mono (by simp))) (by filter_upwards [hβ,h0,hh] with i hβ h0 hh using ⟨hβ,h0,hh⟩)
    have hE:= (hv.bil hc (u:=fun i=>c' i-Y0 i) (Eventually.of_forall (fun i=>by rw [show c' i-Y0 i=f i (c i-U i (Y i)) from (map_sub ..).symm]; exact (f i).le_opNorm (c i-U i (Y i)))))
    exact (RateLE.add (loss _ _ (by linarith only [hσ]) hE) hY hΓ).congr (Eventually.of_forall (fun i=>sub_add_sub_cancel ..))
end algebra


section Physical
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V](r':V→V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E]
    {m:ι→ℕ} (g:ι→ℝ)(hi₀:RateIs l (budgetLog C m) g (-(1/2:ℝ)))
    (tt:Services C F S)(hrank:Module.finrank ℂ V=Module.finrank ℂ (S.Field d))
    (ht:Tendsto m l atTop)
variable (U:ι→ E→L[ℂ] S.Field d) (A:ι→ V→L[ℂ] S.Field d)

local notation "Λ'"=>budgetLog C m
local notation "s'"=>ruler C m
variable {ξ σ:ℝ}{R r:ℕ}
noncomputable def authenticated {H:ι→ V→L[ℂ] Q} (P:ι→(S.Field d→L[ℂ] S.Field d→L[ℂ]ℂ)) (i:ι):=
    (address (H i) (P i)).comp (H i)
variable (Zbook : ι→(S.Field d →L[ℂ] S.Field d→L[ℂ]ℂ))
local notation "AA"=> authenticated d (H:=A) Zbook
local notation "BB"=> fun i=> (address (A i) (Zbook i)).comp (U i)
variable (c:ι→ S.Field d) (Y:ι→E) (Aformal:ℕ→ι→ V→L[ℂ] V→L[ℂ] ℂ)
  (Bformal:ℕ→ι→ E→L[ℂ] V→L[ℂ]ℂ)
    (y:ℕ→ι→ E) (z:ℕ→ι→ V)
set_option synthInstance.maxHeartbeats 60000
set_option maxHeartbeats 560000 in
include tt ht hi₀ hrank in
/-- Main accuracy bridge AFTER soft return. The lower coercivity premises are only on the formal
leading Gram. We use general Gram profile family (instantiate Zbook with that
`receipt` on `unselected` and its `hz` is supplied by PROJECTED ACTUAL `Panel.budget` on
moving K at our diagnostic scale). Keep these readers exposed, no assumption of
`MatrixTicket`. Input c here is in physical reference, and we owe physical match even AFTER taking
this Final (cutoff readings have own filters). Interpreted by `packet_read` etc. Bound `hc` on
that comparison must reach spatial δ beyond d (after paying orientation/tail etc). `ι` can include
ALL normalized Ψ, as in `Layouts`. This is not a physical comparison theorem until furnishing the
input hypotheses exactly. In the core Ledger use V=(Maxwell.freeTable C.labels).Field d or
its coordinates in the nominated pivot basis (fixing metric costs once & for all), apply
`Panel.prices` to the former to get the mirror price. The theorem quantifies over any such
fixed cost vector space, not a varying orientation unbounded space. -/
lemma measured
    (hz: RateLE l s' Zbook (d+d:ℝ))
    (hmoney:∃ b:ℝ,0 ≤ b ∧ (∀ v, ‖r' v‖ ≤ b*‖v‖))
    (hρ:∀ᶠ i in l, ∀ v:V, A i (r' v)= Levy.bar T d (A i v))
    (hx: Attached l Λ' g AA Aformal R ξ)
    (hA: Fits l Λ' Aformal R)(hP:∃ q:ℕ, ∀ᶠ i in l, ∀ v:V, ‖v‖^2 ≤ Λ' i^q * ‖Aformal 0 i v (r' v)‖)
    (hB:Attached l Λ' g BB Bformal R ξ)(he: Fits l Λ' Bformal R)
    (hi: Attached l Λ' g Y y R ξ)(hu: Fits l Λ' y R)
    (hr: Fits l Λ' z R)(hvp:∀ k ≤ R, ∀ᶠ i in l, action Aformal z k i=action Bformal y k i)
    (hc: RateLE l s' (fun i=> c i-U i (Y i)) (-(d:ℝ)-σ))
    (hσ:0<σ)(hx1:ξ < -((r:ℝ)+1)/2)(hq:-((R:ℝ)+1)/2 ≤ ξ)(hle:r≤R)
    :
    (∀ᶠ i in l, Bijective (A i)) ∧ ∃ q:ℕ, ∀ᶠ i in l,
       ‖solve (A i) (c i)-partialSum g r z i‖ ≤ g i^(r+1)* Λ' i^q:=by
    let M : ι→ Q→L[ℂ] (Q→L[ℂ]ℂ):= Zbook; let X:=authenticated d (H:=A) M
    have hg:= tt.simpleGate; have hΓ:= large_Λ C hg ht; have ht':=large_s C ht
    obtain ⟨b,hb,hb'⟩:= hmoney
    have hy:RateLE l s' M (d+d:ℝ):=hz
    refine revision (K:=Λ') («g»:=g) (Z0:=s') (F0:=M) d (A:=A) (U:=U) (Y:=Y) r' hrank hb' hΓ hi₀ ht' (cheap (m:=m) ht hg) (fun v u hu hz=>flat_ignores ht hg v hu hz ξ) (fun p hv h=>to_reference T d ht hρ hy hv h) (by exact hx) hA hP (by exact hB) he hi hu hr hvp hc hσ hx1 hq hle
end Physical
end YM.RGComparison.Core16.Astage.Panel
