import YM.RG17.Tested
import YM.RG17.Cut
import YM.OPE.Short.Vacuum

/-!
# Wires from reports to TRUE readout

Single coupling and convention, no contact prescription. Forecast
ports, NOT a specification sufficient to DEFINE a coefficient system
on their own. Fill by the WilsonX independent (theta-independent
normalized-germ, offset/tuned-column, canonical-A) calculation; existence,
bounds, and verifying the identities below for that prescription at
these shifted readouts OPEN. The adapter is independent of how they are
built, doesn't fit these from the Final. Supports using just enough
precision in the identities at report-radii.

Mixed and pivot input columns read as original separated unselected
products. For reports with K requiring only products of smooth profiles
rather than smooth compact joint profile in Conf, supply the uniform
family/test and relative testing. Smooth exterior tests on S at fixed
physical references; all arities/horizons unbounded formulations can
use the arbitrary-arity theorem below, still NOT growing geometry
or analytic convergence in order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open OPE.Nesting
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S}{L:Layout F} (Z:Ledger L)
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {n:ℕ} {d:Fin n→ℕ}

-- Ports to be populated against shared common preparsed scaling geometry.
structure Ports (C:Family G) where
    marked {n:ℕ} {d:Fin n→ℕ} (slots:(i:Fin n)→ Slot C (d i))(D:ℕ): ℕ→ℝ→ Test n→ C.label D
    moments {n:ℕ} {d:Fin n→ℕ} (slots:(i:Fin n)→ Slot C (d i)): ℕ→ℝ→ Test n→ ℂ
    read (D:ℕ) : ℕ → ℝ → (C.label D→L[ℂ] Free C D)
    ope {n:ℕ} {d:Fin n→ℕ} (slots:(i:Fin n)→ Slot C (d i))(D:ℕ): ℕ→ℝ→ Test n→ Free C D

-- Transport needs BOTH enough perturbative bill on M in full column alphabet,
-- AND spatial comparison on that M. This is at continuum-report interface,
-- AFTER actual signed full-density/exact-law/multi-insertion tests. None of
-- those, nor the ret producer, are automatic. This does NOT allow you to
-- plug in M obtained from density expression in one identity and perturbative
-- remainder purchased on a realignment in another. Use estimates with
-- the retained representative at every step; prove these on that output.
structure Returns (Z:Ledger L) (A:Ports C) (v:(i:Fin n)→ Slot C (d i)) (D:ℕ) (K:Set (Points n)) (p:ℕ) : Prop where
   -- no rechoosing the lens in L; if another regulator subsequence
   -- also needed, check the actual report limits there.
   simultaneous : ∀ W:Finset (External C S),∃ R:ℕ, p<R ∧
     (∀ j≤R, Cost Z (jointTests K) 0 (A.marked v D j)) ∧
     ∃ M:Test n→ℝ→ C.label D, TestedOutput L v D W K M ∧
       Cost Z (jointTests K) R (fun r ψ=> M ψ r - forecast Z R (A.marked v D) r ψ)

abbrev send0 (C:Family G) : C.label 0→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap (LinearMap.proj 0)
structure VacuumCompat (Z:Ledger L) (A:Ports C) (v:(i:Fin n)→ Slot C (d i)) (K:Set (Points n)) (p:ℕ) : Prop where
    cap : ∀ j≤p,Cost Z (jointTests K) 0 (A.moments v j)
    relation : ∀ q:ℕ,q ≤ p → Cost Z (jointTests K) (q+1) (fun r ψ=> send0 C (forecast Z q (A.marked v 0) r ψ) - forecast Z q (A.moments v) r ψ)

-- true full correlations (relative test, already in S). Keep even in variant viewers.
def measured (F:Final C f S)(v:Labels S d)(r:ℝ)(view:Viewers F) (ψ:Test n):ℂ:=
    ψ.applyTo fun x=> Orbits.moment (spectator F view) (posed r x) v

local notation "UP"=>upon (S:=S)
abbrev vacTags (S:Table C.book) := fun z:Empty=> (OPE.Short.extra (z:=z):S.Tag)
def blank (F:Final C f S)(view:Viewers F) : S.Field 0→L[ℂ]ℂ := LinearMap.toContinuousLinearMap (upon (spectator F view) 0 0 OPE.Short.gapPos (voices (vacTags S)))
include Z
lemma blank_reads (z:S.Field 0) (view:Viewers F): blank F view z=blank F none z:=by
   obtain ⟨c,h⟩:= RG12.unit_spans Z.simple C 0 (C.ref 0) (by norm_num) (S.representative 0 z) -- Z not included
   have hk : z=c• S.unit 0:=by rw [←S.rep 0 z,h,map_smul]; rfl
   rw [hk,map_smul,map_smul]; exact congr_arg (c • ·) ((OPE.Short.vacuum F view 0 0 (vacTags S)).trans (OPE.Short.vacuum F none 0 0 (vacTags S)).symm)
lemma blank_master (hL:Located L) : ∀ᶠ r in home,∀ x,blank F none (master L 0 r x)= send0 C x := by
   filter_upwards [Z.reach.growing.eventually_ge_atTop (C.ref 0), hL.unit₀] with r hr hs x; let k:=L.level r
   let u:= (C.labels.level 0).e0
   let h:Source.unitVec (C.labels.level 0) C.path k=u:= by simp only [Source.unitVec,pow_zero,one_smul,u]
   obtain ⟨c,hx⟩:= RG12.unit_spans Z.simple C 0 k (by norm_num) x
   rw [h] at hx
   have he: master L 0 r u=S.unit 0:=by
       letI : L.lens.NeBot := L.notbot
       change RG12.engineering _ _ _ (L.shift _ _ u)=_
       rw [hs,RG12.engineering_at, ← show _=(C.labels.level 0).e0 from h,L.observes.unit 0 (L.level r) hr]; simp only [pow_zero,map_one,one_smul,Complex.ofReal_one]; rfl
   rw [hx,map_smul,map_smul,he,map_smul]
   have hs':blank F none (S.unit 0)=1:= OPE.Short.vacuum F none 0 0 (vacTags S); rw [hs']
   congr 1
omit Z
lemma posed_on {x:Points n}{r:ℝ}(hx:x∈conf n)(hr:0<r): Injective (posed r x):=fun _ _ he=> hx ((smul_right_injective E4 hr.ne') he)
lemma empty_profile (v:Labels S d){r:ℝ}(hr:0<r)(view:Viewers F) {ψ:Test n} (hp: tsupport ψ ⊆ conf n):
    query F v OPE.Short.gapPos (voices (vacTags S)) view r ψ=measured F v r view ψ:=by
    apply integral_congr_ae; filter_upwards with x; by_cases h:x∈tsupport ψ
    · refine congr_arg (fun z:ℂ=> ψ x*z) ?_
      exact OPE.Short.tagged F (tags v) (posed r x) view (posed_on (hp h) hr)
    change ψ x * _ = ψ x* _; rw [image_eq_zero_of_notMem_tsupport h]; simp

include P Z
lemma horizonZero {A:Ports C} {v:(i:Fin n)→ Slot C (d i)} (h:Services C f S)(hL:Located L) {K:Set (Points n)}(hc:IsCompact K)(hk:K⊆conf n) {p q:ℕ}(hq:q ≤ p)(C₀: VacuumCompat Z A v K p)(hV: Returns Z A v 0 K p) :
    Cost Z (joins K (Viewers F)) (q+1) (fun r (x:Viewers F × Test n)=> measured F (stems L v r) r x.1 x.2 - forecast Z q (A.moments v) r x.2):=by
   obtain ⟨W,H⟩:= spatialLocated P L h hL v 0 hc hk
   obtain ⟨j,hj,hb,M,hM,hqM⟩:= hV.simultaneous W
   have hx:=Cost.openTerm (lt_of_le_of_lt hq hj) (fun i _ hi=>hb i hi) hqM
   obtain ⟨b,X,k,hb,hX,H⟩:= H M hM
   let U r ψ:= basket P 0 (stems L v r) r ψ
   have hB: Cost Z (jointTests K) (q+1) (fun r ψ=>U r ψ-master L 0 r (M ψ r)):=by
      have he:RateLE home OPE.run (fun r=> X*r^b) (-b):=by
         simpa only [mul_neg_one,zero_add] using (RateLE.const X ageLarge).mul ((lengthRate.rpow b).pays ageLarge)
      exact Cost.coarse (neg_lt_zero.mpr hb) _ (fun r=>X*r^b) he k (H.mono fun r hr ψ a ⟨ht,hψ⟩=>by simpa only [Nat.cast_zero,zero_add] using hr ψ ht a hψ)
   let M₀:= blank F none
   have hv:= ((hB.capture M₀).add (hx.capture (send0 C))).add (C₀.relation q hq)
   have he: Cost Z (jointTests K) (q+1) (fun r ψ=>M₀ (U r ψ) - forecast Z q (A.moments v) r ψ):=by
       apply hv.congr; filter_upwards [blank_master Z hL] with r hr ψ
       simp only [map_sub]; rw [(show M₀ _=send0 C (M ψ r) from hr _)]; abel
   let w:= voices (vacTags S); let y:=OPE.Short.gapPos; have hW:ClearOf 0 y 1:= ⟨fun i=> i.elim,fun i=>i.elim⟩
   have hz:= testedPacketLocated P L h hL v 0 hc hk (ε:=1/2) (by norm_num) zero_lt_one w
   have h': Cost Z (joins K (Viewers F)) (q+1) (fun r x=> measured F (stems L v r) r x.1 x.2 - M₀ (U r x.2)) := by
       refine Cost.coarse (b:= -(1/2:ℝ)) (by norm_num) _ (fun r=> r^(1/2:ℝ)) (((lengthRate.rpow _).pays ageLarge).mono (by norm_num)) 0 ?_
       filter_upwards [positiveLength,hz] with r hr hv x a ⟨hψ,hA⟩
       rw [← empty_profile (r:=r) (ψ:=x.2) _ hr x.1 (hψ.trans hk),← show blank F x.1 _ = M₀ _ from blank_reads Z (U r x.2) x.1]
       apply le_trans (hv x.2 hψ y hW x.1)
       norm_num -- exponent
       try ring_nf
       exact mul_le_mul_of_nonneg_left hA.norm (Real.rpow_nonneg hr.le _)
   apply (h'.add (Cost.uniform Z _ _ _ Prod.snd (fun _ _ _ hp=> hp) he)).congr; exact Eventually.of_forall fun r x=>by abel
end YM.RG17
