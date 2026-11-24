import YM.RG17.Rim

/-!
Detector and THIN comparison hypotheses for leading/radiative. On the TRUE
portrait. Here use leading reference `metric0` convention, and calibration
at measurement LENGTH (= radius); if coming from A at m with polylog spacing
salary, not automatic that those panels can be aligned and costed in this
convention to the precision required. Wgt still Z.g in all tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Set Function Filter MeasureTheory Table Spec Extraction OPE OPE.Orbits
open Points Trace
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G} {f:Extraction.Order}{S:Table C.book}{F:Final C f S} {n:ℕ}

abbrev φS (C:Family G) : Free C 4:= Trace.scalarLabel C.labels
abbrev refForce (C:Family G)(ψ:Test 2):= ψ.applyTo (swipe (S:=Maxwell.freeTable C.labels) 1 (φS C) (φS C) timeAxis)
lemma someRim (C:Family G)(hG:G.Simple) :∃ N:Rim,refForce C N.test≠0:=by
   let M:=Maxwell.freeTable C.labels; let v:=φS C
   let h:=Maxwell.Free.hierarchy C.labels
   let k:=swipe (S:=M) 1 v v timeAxis
   have hk : ContinuousOn k (conf _):= swipe_cont _ _ one_pos _ (h)
   let x:=separated 1; have hx : x∈conf 2:=room_conf _ _ _ _ _ (room_separated _ zero_le_one) one_pos one_pos
   obtain ⟨U,χ,hW,he,hU,hV,hΦ⟩:=Rim.accommodates hx
   have he : ∃ g:Points 2→ℝ,ContDiff ℝ ∞ g∧HasCompactSupport g∧tsupport g⊆U ∧ (∫ y,g y • k y) ≠ 0:=by
       by_contra! hp
       have hk':= Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr (hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume) ((hk.mono hV).locallyIntegrableOn hU.measurableSet) hp)) hU (hk.mono hV) continuousOn_const
       apply (show k x≠0 from ?_) (hk' he)
       have hc:k x= _:= reduceSwipe (S:=M) v v (r:=1) one_pos timeAxis h hx
       simp only [one_smul, bilim,show Fin.cons (α:=fun _:Fin 2=>M.Tag) ⟨4,v⟩ (fun _:Fin 1=>⟨4,v⟩)=scalarCompar (C:=C) from funext fun i=> by fin_cases i <;> rfl] at hc
       change k x = gradient 0 _ (Ward.disc (scalarCompar (C:=C))) _ at hc
       rw [hc,Trace.free_rate]; exact_mod_cast (show (8:ℝ)*theoryDensity G≠0 by positivity [theoryDensity_pos hG])
   obtain ⟨g,hg,hc,hk,he⟩:= he
   let V:Points 2→ℂ:= fun x=> (g x:ℂ)
   have hs : tsupport V=tsupport g:=by unfold tsupport; rw [show support V = support g from by ext x; simp [V]]
   let ψ:Test 2:= ⟨V,Complex.ofRealCLM.contDiff.comp hg, show IsCompact _ from hs.symm ▸ hc, (show tsupport V⊆conf 2 from hs.symm ▸ (hk.trans hV))⟩
   exact ⟨⟨ψ,χ,hW.1,hW.2.1,fun x hx=>hΦ _ (hk (hs ▸ (show x∈tsupport V from hx)))⟩, by simpa only [Complex.real_smul] using! he⟩

set_option maxHeartbeats 600000 in
lemma metric_match (C:Family G) : StressLaws (Maxwell.freeTable C.labels) (S:=Maxwell.freeTable C.labels) (metric0 C.labels) (Maxwell.Free.scheme C.labels).deriv (Maxwell.Free.gear C.labels).lie:=by
   have hf:=Maxwell.Free.beacon_signal C.labels (-1)
   rw [neg_neg,one_smul,one_smul,← Pert.common_stress] at hf
   rw [show (-1:ℝ) • UVNext.FreeStress.torch C.labels 1=metric0 C.labels from funext (fun i=> funext fun j=> by rw [neg_smul,one_smul]; exact congr_arg Neg.neg (one_smul ℝ _))] at hf
   exact hf

variable {L:Layout F} (Z:Ledger L) (A:Ports C)
set_option quotPrecheck false
local notation "P!" => portal L
local notation "M!" => Maxwell.freeTable C.labels
abbrev sentTest (v: Fin n→Free C 4)(ψ:Test n)(p:ℕ)(r:ℝ):= forecast Z p (A.moments (d:=fun _=>4) (fun i=> Sum.inr (v i))) r ψ
noncomputable def τestimate (ψ:Test 2)(r:ℝ) :ℂ := (-∑ i:Axis,sentTest Z A (![metric0 C.labels i timeAxis,φS C]) (direct i ψ) 2 r )/ (Z.g r:ℂ)^2

-- These clauses only on diagram ports. **Must still compute the Ward coefficient** in WilsonX.
-- `signal` sufficient radiative input, full signed/kinetic calculations there open.
structure Passage (Z:Ledger L)(A:Ports C) : Prop where
    begins (n:ℕ) (hn:n≤3) (v:Fin n→ Free C 4)(ψ:Test n) : Tendsto (fun r=> sentTest Z A v ψ 0 r) home (𝓝 (plate (S:=M!) (d:=fun _=>4) v 1 ψ))
    signal (ψ:Test 2) : Tendsto (τestimate Z A ψ) home (𝓝 ((anomalyCoefficient G / 2) • refForce C ψ))
structure Tide (Z:Ledger L)(A:Ports C) : Prop where
    follows (n:ℕ) (hn:n≤3) (v:Fin n→Free C 4) (ψ:Test n) :
       let v': (i:Fin n)→ Slot C ((fun _=>4) i):= fun i=> Sum.inr (v i)
       Returns Z A (d:=fun _=>4) v' 0 (tsupport ψ) 2 ∧ VacuumCompat Z A v' (tsupport ψ) 2

lemma pays {a:ℝ→ℂ}{p:ℕ}(h:Bare Z (p+1) a) : Tendsto (fun r=>a r/(Z.g r:ℂ)^p) home (𝓝 0):=by
   obtain ⟨c,i,hc,hM⟩:=Cost.bound_single h
   refine squeeze_zero_norm' (f:=fun r=>a r/(Z.g r:ℂ)^p) (a:=fun r=>c*(Z.g r*Z.Λ r^i)) ?_ (by simpa only [mul_zero] using (Z.dominant i).const_mul c)
   filter_upwards [hM] with r hr; have h':= Z.positive r; rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg h'.le]; exact ((div_le_iff₀ (by positivity)).mpr (hr.trans_eq (by rw [pow_succ]; ring)))
variable (H:Services C f S) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (loc:Located L) (V:Tide Z A) (Q: Passage Z A)
include P H loc V
lemma surf (v: Fin n→Free C 4)(hn:n≤3)(ψ:Test n)(p:ℕ)(hp:p≤2) : Bare Z (p+1) (fun r=>
    plate (d:=fun _=>4) (fun i=> P! r (v i)) r ψ - sentTest Z A v ψ p r):=by
    obtain ⟨h,h'⟩:=V.follows n hn v ψ
    let K:=tsupport ψ; let x : Viewers F × Test n:= (none,ψ)
    have hk (j:ℕ):∃ a:ℝ,(joins K (Viewers F)).pay j x a:=by
        obtain ⟨a,ha⟩:= demandAccessible j ψ; exact ⟨_,subset_rfl,ha⟩
    apply ((horizonZero Z P H loc ψ.hasCompactSupport ψ.tsupport_subset hp h' h).incurs x hk).congr
    filter_upwards [positiveLength] with i hi _; rw [physicalPlate F _ _ hi]; rfl
include Q
lemma wave_zero (v: Fin n→Free C 4)(hn:n≤3)(ψ:Test n) : Tendsto
    (fun r=>plate (d:=fun _=>4) (fun i=>P! r (v i)) r ψ) home (𝓝 (plate (S:=M!) (d:=fun _=>4) v 1 ψ)):=by
    have hv:= (pays Z (surf Z A H P loc V v hn ψ 0 (by decide))).add (Q.begins n hn v ψ); rw [zero_add] at hv; exact hv.congr (fun i=> by simp)

lemma scalar_limit (ψ:Test 2): Tendsto (fun r=> force P! ψ r (scalarRay P! r)) home (𝓝 (refForce C ψ)):=by
    have hk:= (wave_zero Z A H P loc V Q (![φS C,φS C] : Fin 2→ Free C 4) (by decide) (direct timeAxis ψ)).neg
    rw [← show refForce C ψ= _ from sift (S:=M!) _ _ (r:=1) one_pos _ (Maxwell.Free.hierarchy C.labels) ψ] at hk
    refine hk.congr' (positiveLength.mono fun r hr=> ?_)
    change _=ψ.applyTo (swipe r (scalarRay P! r) (scalarRay P! r) timeAxis)
    rw [sift _ _ hr _ F.room.kernel]; apply congr_arg Neg.neg; refine congr_arg (fun v:Fin 2→S.Field 4=> plate (d:=fun _=>4) v r _) (funext fun i=>?_); fin_cases i <;> rfl
lemma translate_test (N:Rim): Tendsto (fun r=>N.Qstress L r (scalarRay P! r)) home (𝓝 (refForce C N.test)):=by
    let H':=Maxwell.Free.hierarchy C.labels
    have ht(i:Axis): Tendsto (fun r=> N.stressBill L r (scalarRay P! r) i) home (𝓝 (Rim.price (S:=M!) N (φS C) i (metric0 C.labels i timeAxis) 1)):=by
        apply (wave_zero Z A H P loc V Q (![metric0 C.labels i timeAxis,φS C,φS C]) (by decide) (N.armed i)).congr (fun r=> ?_)
        apply congr_arg (fun v:Fin 3→S.Field 4=>plate (d:=fun _=>4) v r _); funext i; fin_cases i <;> rfl
    rw [show refForce C N.test=_ from Rim.stress_cut (S:=M!) N _ (r:=1) one_pos H' _ _ (Maxwell.Free.scheme_derives _) _ (metric_match C)]
    simp_rw [one_pow, one_smul]; exact (tendsto_finsetSum Finset.univ (fun i _=>ht i)).neg
lemma pse_test (N:Rim): Tendsto (fun r=> N.Qscalar L r (scalarRay P! r)) home (𝓝 (-N.price (S:=M!) (φS C) timeAxis (φS C) 1)):=by
    refine (wave_zero Z A H P loc V Q (![φS C,φS C,φS C]) (by decide) (N.armed timeAxis)).neg.congr (fun r=> ?_)
    apply congr_arg Neg.neg; apply congr_arg (fun v:Fin 3→S.Field 4=> plate (d:=fun _=>4) v r _); funext i; fin_cases i <;> rfl
lemma shift_limit (ψ:Test 2): Tendsto (fun r=> shiftAll P! ψ r (scalarRay P! r) / (Z.g r:ℂ)^2) home (𝓝 ((anomalyCoefficient G/2) • refForce C ψ)):=by
   let f (i:Axis) r:=sentTest Z A (![metric0 C.labels i timeAxis,φS C]) (direct i ψ) 2 r
   have hh (i:Axis): Bare Z 3 (fun r=>shiftPair P! i ψ r (scalarRay P! r)+f i r):=by
       apply Cost.transfer (surf Z A H P loc V (![metric0 C.labels i timeAxis,φS C] : Fin 2→ Free C 4) (by decide) (direct i ψ) 2 le_rfl)
       filter_upwards [positiveLength] with r hr _
       let y:=scalarRay P! r;let x:=tensorRay P! r i timeAxis
       change ‖ψ.applyTo _+_‖≤_
       rw [sift _ _ hr _ F.room.kernel]
       have he : (fun j:Fin 2=>P! r ((![metric0 C.labels i timeAxis,φS C]) j))=![x,y]:=funext fun i=>by fin_cases i <;> rfl
       rw [he]; change ‖-plate (d:=fun _=>4) ![x,y] r _ +f i r‖≤‖_ -f i r‖; rw [←neg_sub _ _] -- check
       rw [norm_neg]; rw [add_comm]; rw [sub_eq_add_neg]
   have hk:Bare Z (2+1) (fun r=> ∑ i:Axis,(shiftPair P! i ψ r (scalarRay P! r)+f i r)):= Cost.sum (H:= Finset.univ) (fun i _=>hh i)
   have he:= (pays Z hk).add (Q.signal ψ); rw [zero_add] at he; apply he.congr (fun i=> ?_); rw [Finset.sum_add_distrib,add_div]; unfold shiftAll τestimate f; ring
end YM.RG17
