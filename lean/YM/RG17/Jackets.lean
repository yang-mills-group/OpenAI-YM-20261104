import YM.RG17.Launches
/- Overshoot combined result. Fold across ALL n< cutoff. Need all-flag gain still. Do not silently use unborn stamps. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Finset Spec Lattice Wilson Next.UVStress MergeProof
open PhysicalNext PhysicalNext.Repeat.Legato OPE OPE.Orbits RG Next.Rank Extraction Cells Marker SharpGram MeasureTheory Overlay
open scoped Topology Classical BigOperators
set_option quotPrecheck false
variable {G:Gauge}(R:Run G) {f:Extraction.Order}{S:Table R.family.book}{F:Final R.family f S}{L:Layout F} {n:ℕ}(W:Ledger L)(fx:Flick R.family.path.levels) {r:ℝ}{x:Points n}(d:Fin n→ℕ)(v:(i:Fin n)→ Free R.family (d i))
local notation "C"=> R.family
local notation "a"=> R.family.S.a
local notation "ρ"=> wheel R.family
local notation "θ"=> role R.family
local notation "A"=> R.family.path
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "M"=> L.level
def rake (b:Fin n → Cover)(r:ℝ)(u:(ℕ×ℕ)): Fin n → Site (R.family.side u.1 u.2):= attachV R (p:=u.2) (ρ r) (wrap _ ∘ b) u.1
lemma rato (u:(ℕ×ℕ)) (h:ρ r ≤ u.1)(b:Fin n → Cover): rake R b r u= Cells.location R.family.S (ρ r) u.1 u.2 ∘ b:=by
    funext i; unfold rake attachV Cells.location; dsimp only [Function.comp_apply]; rw [dif_pos h]; exact Ribbons.vect .. -- hm?

variable {B : Filter (ℕ×ℕ)}{D:Lenses.Mantle F B} {s:Extraction.Sequence}
include R W fx
open SharpGram.Allow
private lemma feeder : ∀ᶠ r in home,H (M r) ≤ H (ρ r)^2:=by
   have ht:= Gauge.slopeConstant_pos W.simple
   have hV: Tendsto (fun r=> H (M r) / H (ρ r)) home (𝓝 1):=by
       have he:= (tollRatio W.reach).div (tollRatio (opt _ fx W.simple)) ht.ne'; rw [div_self ht.ne'] at he; apply he.congr'; filter_upwards [ageLarge.eventually_gt_atTop 0] with r hr
       exact div_div_div_cancel_right₀ hr.ne' _ _
   filter_upwards [hV.eventually (ge_mem_nhds one_lt_two), ((Station.hat_rate _ W.simple).comp (turnsWheel C)).eventually_ge_atTop 2] with r hv hQ
   have hh:0<H (ρ r):=zero_lt_one.trans ((A).levels.fits.delayed _); refine ((div_le_iff₀ hh).mp hv).trans ?_; have hp':2 ≤ H (ρ r):= hQ; nlinarith only [hp']

variable (E:Services R.family f S)(h:Stands L D s)
local notation "T"=> interval D s
include E h d v
lemma grantedWays : ∃ (i:ℕ)(w:ℝ→(j:Fin n)→ R.family.label (d j)), ∀ᶠ r in T, ∀ j,Paid L r (w r) j ≤ H (ρ r)^i ∧ master L _ r (w r j)= L.frame (d j) r (v j):=by
   obtain ⟨w,H'⟩:=individual E h.pegs v
   obtain ⟨i,hi⟩:= (eventually_all.mpr fun j:Fin n=>eventually_ge_atTop (2*Lenses.price (d j)+1)).exists
   have hx:T ≤ home:= (homes D).comp s.cofinal
   refine ⟨i,w,hx ?_⟩
   have hc:Tendsto (fun r=>H (ρ r)) home atTop:= (Station.hat_rate _ W.simple).comp (turnsWheel C)
   filter_upwards [feeder R W fx,H',eventually_all.mpr (fun j=>hc.eventually_ge_atTop (2*‖v j‖))] with r hr hC hx j
   have hv: (1:ℝ) ≤ H (ρ r):= ((A).levels.fits.delayed _).le
   refine ⟨(hC.1 j).trans (le_trans ?_ (pow_le_pow_right₀ hv (hi j))),hC.2 j⟩
   have hL := pow_le_pow_left₀ (zero_lt_one.trans ((A).levels.fits.delayed _)).le hr (Lenses.price (d j))
   rw [← pow_mul] at hL; rw [pow_succ]
   calc _ = H (M r)^ _ * (2 * ‖v j‖) := by ring
        _ ≤ _:= mul_le_mul hL (hx j) (by positivity) (pow_nonneg (zero_le_one.trans hv) _)

-- physical points ghost with actual weight.
abbrev receiptLine (b:Fin n → Cover)(w:(i:Fin n)→ R.family.label (d i))(r:ℝ)(p:(ℕ×ℕ)):=R.family.numeric p.1 p.2 (shutter R L d r p.1 p.2 w) (rake R b r p)

set_option maxHeartbeats 600000 in
lemma erectedNow {i:ℕ}{w:ℝ→ (j:Fin n)→ R.family.label (d j)}(H':∀ᶠ r in T, ∀ j,Paid L r (w r) j ≤ H (ρ r)^i ∧ master L _ r (w r j)= L.frame (d j) r (v j)): ∀ (x:Points n)(b:ℝ→ Fin n → Cover), x∈generic n → Tendsto (fun r=>tag (θ r) (b r)) T (𝓝 x) → (∀ᶠ r in T,Tendsto (receiptLine (L:=L) R d (b r) (w r) r) L.lens (𝓝 (S.useAt S (r • tag (θ r) (b r)) (tags (d:=d) (fun i=> L.frame _ r (v i)))))) ∧
   ∀ j:ℕ, ∃ Q:ℝ,0≤ Q ∧ ∀ᶠ r in T,∀ᶠ p in L.lens, let N:= p.1; let t:=p.2; let k:=ρ r; let z:= wrap ((C).side k t) ∘ b r; let x:= rake R (b r) r p; let y:= shutter R L d r N t (w r); let U':= pullDimes y (N:=N) (p:=t) x (Stock.final (Fin n)) k; receiptLine (L:=L) R d (b r) (w r) r p=(∫ V,U' V∂prior ..)/(keyMass C N t:ℂ) ∧
       ∀ U,flags (A|>.rep N t k).p.threshold U=∅→ ‖U' U/(boardMass C N t k U:ℂ) - ∏ i:Fin n,lines17 y (p:=t) (attachV R k z) N k i U‖ ≤ Q * Pert.Asymptotics.regulatorRun C N t k ^ (2*j):=by
    have hl:T ≤ home:= (homes D).comp s.cofinal
    intro x b he hp
    have ht:= launches W fx hl hp he
    haveI := L.notbot
    have hh:∀ᶠ r in T,∀ i:Fin n,R.family.ref (d i) ≤ M r:= (eventually_all.mpr fun i:Fin n=> W.reach.growing.eventually_ge_atTop (R.family.ref (d i))).filter_mono hl
    constructor
    · filter_upwards [ht,H',hh,positiveLength.filter_mono hl] with r hr hc hi hu
      rw [scaledRole hu]; let z:=tag (R.family.S.a (ρ r)) (b r); let Y : R.family.book.Vector d:=fun j=> locatedRef L (d j) r (w r j)
      let t(p:ℕ×ℕ) : R.family.book.Vector d:= fun j=> atRef L (d j) r p (w r j)
      have hx:tag (R.family.S.a (ρ r)) (b r)∈generic n:=hr.1
      have hp(j:Fin n):= tendsRef L (show L.lens ≤ _ from le_rfl) (v:=fun _=> w r j) tendsto_const_nhds (hi j) -- typo
      have hh:= Cards.variation («C»:=R.family) (k:=ρ r) (b r) F.room.generic hx Y t (fun j=>hp j) L.certified
      have hv:Tendsto (fun p:(ℕ×ℕ)=> R.family.numeric p.1 p.2 (shutter R L d r p.1 p.2 (w r)) (Cells.location R.family.S (ρ r) p.1 p.2 ∘ b r)) L.lens (𝓝 (S.value d z Y)):= hh
      rw [show S.useAt _ _ _= S.value d z Y from ?_]
      · apply hv.congr'
        filter_upwards [(large_mesh f (ρ r)).filter_mono L.certified] with p hJ
        dsimp only [receiptLine]
        rw [rato R p hJ]
      let u: Fin n→ R.family.book.Token:= fun j=> ⟨d j,Y j⟩
      have ha:tags (d:=d) (fun j=> L.frame (d j) r (v j))=S.classTokens ∘ u:=by
          funext j; exact congr_arg (Sigma.mk (β:=S.Field) (d j)) (((payRef L _).trans (hc j).2).symm)
      rw [ha]; exact S.at_project _ F.room.kernel.laws.toSymmetric (fun _=>le_refl _) (generic_conf _ hr.1) u
    intro j; obtain ⟨Q,hQ,hB⟩:= allClear (Γ:= Stock.census (Fin n) ) R fx L E d 8 i j
    have hv:∀ᶠ r in T,a (M r) ≤ r:=by
       change ∀ᶠ i:ℕ in atTop,a (M (offsetPath D s i))≤ offsetPath D s i
       filter_upwards [s.cofinal.eventually D.proper] with i hi
       change a (M (offsetPath D s i))≤ _; rw [h.match_length]; exact hi.1
    refine ⟨Q,hQ,?_⟩
    filter_upwards [ht,H',hv,(turnsWheel C|>.mono_left hl).eventually hB, (reverseSpoke C fx W.simple).filter_mono hl,hh] with r hr hV hE he hx hh
    filter_upwards [hr.2, (large_mesh f (M r)).filter_mono L.certified,(large_mesh f (ρ r+1)).filter_mono L.certified] with p hz hM hk N t k z x y A₀
    have hk' : k<N:= hk; let P:= keyMass C N t
    constructor
    · change (R.family.numeric N t y x)=(∫ V, pullDimes y x (Stock.final (Fin n)) k V∂ prior G _)/(P:ℂ)
      rw [show (∫ V,pullDimes y x (Stock.final (Fin n)) k V∂ prior G _)=_ from (fullDimes («C»:=R.family) (N:=p.1) (p:=p.2) R.makes y x hk'.le),mul_comm]; exact (mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')).symm
    have h': a (M r) / a k ≤ H k^8 := (div_le_iff₀ (R.family.S.a_pos _)).mpr ((hE.trans hx).trans_eq (mul_comm ..))
    intro U hU; exact he _ _ hk' r hM hh h' _ (fun j=> (hV j).1) z (fun _ _ h=>hz h) U hU (Stock.final (Fin n))
lemma erectedPrices : ∃ (w:ℝ→ (j:Fin n)→ R.family.label (d j)),∀ (x:Points n)(b:ℝ→ Fin n → Cover), x∈generic n → Tendsto (fun r=>tag (θ r) (b r)) T (𝓝 x) → (∀ᶠ r in T,Tendsto (receiptLine (L:=L) R d (b r) (w r) r) L.lens (𝓝 (S.useAt S (r • tag (θ r) (b r)) (tags (d:=d) (fun i=> L.frame _ r (v i)))))) ∧
   ∀ j:ℕ, ∃ Q:ℝ,0≤ Q ∧ ∀ᶠ r in T,∀ᶠ p in L.lens, let N:= p.1; let t:=p.2; let k:=ρ r; let z:= wrap ((C).side k t) ∘ b r; let x:= rake R (b r) r p; let y:= shutter R L d r N t (w r); let U':= pullDimes y (N:=N) (p:=t) x (Stock.final (Fin n)) k; receiptLine (L:=L) R d (b r) (w r) r p=(∫ V,U' V∂prior ..)/(keyMass C N t:ℂ) ∧
       ∀ U,flags (A|>.rep N t k).p.threshold U=∅→ ‖U' U/(boardMass C N t k U:ℂ) - ∏ i:Fin n,lines17 y (p:=t) (attachV R k z) N k i U‖ ≤ Q * Pert.Asymptotics.regulatorRun C N t k ^ (2*j):=by
    obtain ⟨i,w,H'⟩:=grantedWays R W fx d v E h
    exact ⟨w,erectedNow R W fx d v E h H'⟩
end YM.RG17
