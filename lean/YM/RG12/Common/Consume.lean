import YM.RG12.Common.Capture
/-!
# Sharp physical OPE consuming ONLY outstanding adjacent reflected price hypotheses

Dyadic consecutive prices (unit natural log spacing here), and weak length-window costs on the
same fields to couple to our UNCONDITIONAL lamp data. Uses the same constructions, scale gates
and quantities, arbitrary Final from package. No independent assumption about what happens in
interiors or k-capture-to-reference comparison. The dyadic and between hypotheses remain
conditional; need actual measurements on these specified comparable-scale tests to at least
O(1/logAge) between unit-log scale pairs, and polynomial costs elsewhere, not full-history
WilsonX. Exact hypotheses below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche.Drives
open Function Filter Set Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Station Real Asymptotics Ship Peak
open PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof MergeProof.East Next.Rank.Tapes.West MergeProof.Accent
open Pert.Dense Spec Bid YM.RG12.Arche YM.RG12.Commission Desk Desk.Paired Sample OPE
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}
variable {M:∀ d,ℕ→RepChart C d} {ϕ:Filter UVIndex} [ϕ.NeBot]
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "κ" k:max=> C.S.a k
local notation "chol"=> (A).clock.hatBeta
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S) (ax:Axis)
variable (h:Observing C F.room.cutoff ϕ M) (he : ϕ  ≤  f.fuse)
variable (P:Port C)(hp:Covered P F.room.cutoff) (H:G.Simple) (L:Facilities C f S)
local notation "B!"=>F.sector.derivatives
-- address to sample for any supported k prices
private def spot (t:ℝ) := Nat.floor (-Real.log t)
private lemma touches {t:ℝ}(ht:0<t)(hr:t  ≤  1): Sample.length (spot t+1)  ≤  t ∧ t  ≤  Sample.length (spot t) ∧ Sample.length (spot t)  ≤  Sample.ratio (spot t)*t:=by
   let s:= -Real.log t; have he:0 ≤ s:= neg_nonneg.mpr (Real.log_nonpos ht.le hr); have hl: (spot t:ℝ)  ≤  s:= Nat.floor_le he; have hh:s  ≤  (spot t:ℝ)+1:=(Nat.lt_floor_add_one s).le
   nth_rw 2 [← Real.exp_log ht]; -- messy
   change Real.exp (-((spot t+1:ℕ):ℝ))  ≤  _ ∧ _  ≤  Real.exp (-↑(spot t)) ∧ Real.exp (-↑(spot t))  ≤  Real.exp 1*_
   constructor; · exact Real.exp_monotone (show -((spot t+1:ℕ):ℝ) ≤ Real.log t by push_cast; linarith only [hh])
   constructor
   · exact le_trans (Real.exp_log ht).symm.le (Real.exp_monotone (by linarith only [hl]))
   nth_rw 2 [← Real.exp_log ht]; rw [← Real.exp_add]; exact Real.exp_monotone (by linarith only [hh])

private lemma smallness {t:ℕ→ℝ}(ht:Tendsto t atTop (𝓝 0))(h:∀ᶠ k in atTop,(κ k)  ≤  t k):
    Tendsto (fun k=>spot (t k)) atTop atTop:=by
   have hv:Tendsto t atTop (𝓝[>]0):= tendsto_nhdsWithin_iff.mpr ⟨ht,h.mono fun k hk=> (C.S.a_pos k).trans_le hk⟩
   exact tendsto_nat_floor_atTop.comp (tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp hv)) -- name
include H
private lemma ages {t:ℕ→ℝ}(h:∀ᶠ k in atTop,(κ k)  ≤  t k):
    ∀ᶠ k in atTop, Sample.age (spot (t k))  ≤  (chol k)^2 :=by
   filter_upwards [(Sample.enough_stops C H 0 0),h] with k hk hh
   obtain ⟨hs⟩:=hk
   have he:0  ≤  C.S.scale k:= by rw [← Schedule.scale_zero (S:=C.S)]; exact scale_mono (A) (Nat.zero_le k) -- wrong
   have hi: -(Real.log (t k))  ≤  C.S.scale k:=by have hy:= Real.log_le_log (C.S.a_pos k) hh; rw [Stock.a_log,Real.log_exp] at hy; linarith only [hy]
   exact (show Sample.age (spot (t k))  ≤  Sample.age (Sample.atMesh C k) by unfold Sample.age; have hx: spot (t k)  ≤  Sample.atMesh C k:= Nat.floor_le_floor hi; exact add_le_add_left (Nat.cast_le.mpr hx) _).trans hs.clock

def survey (S : Table C.book)(F:Final C f S)(ax:Axis)(N d:ℕ)(t:ℝ) := Real.sqrt ∘ (sampleForm F (Shapes.scope ax N) d t).eval
/-- Independent open input. No k calibration or capture leakage: every demand here is exposed
purely in S and on bounded length ratio. In `between` can e.g. test on the same dyad Y pivots
at each length t with coercivity and upper estimates in the same pivot norm (constants or
bounded powers of n); that gives the form here automatically by invertibility in Tests (use
Frames.enough). N can be any sufficiently large smoothing parameter, associated to exact
positions in `Shapes`. -/
def March (Q:Prescription B!) (hq:Q.Coherent) (d : ℕ): Prop :=
  let V:= Sector B! d
  ∀ᶠ N:ℕ in atTop, let R:=survey S F ax N d; let T i:= R (Sample.length i)
    ∃ (Y : ℕ → Frames.Col V →ₗ[ℂ] S.Field d)(J:ℕ → Frames.Col V ≃ₗ[ℂ] Frames.Col V)
      (K:ℝ)(p b a n₀:ℕ), Frames.Consecutive Sample.age Sample.length Sample.ratio Y (Desk.official Q hq d) T J K p b n₀ ∧
      ∀ n:ℕ,n₀  ≤  n→∀ t:ℝ, Sample.length (n+1)  ≤  t →t  ≤  Sample.length n→∀ v : S.Field d,
       R t v  ≤  Sample.age n^a * T n v ∧ T n v  ≤  Sample.age n^a * R t v
include P hp H h he L
lemma applyAt (Q:Prescription B!)(hq:Q.Coherent)(d:ℕ)(hx:March F ax Q hq d):
    RightPrice C S M d∧∀ w,RowPrice C S B! M d w:=by
   obtain ⟨N,hN⟩:= eventually_atTop.mp hx
   obtain ⟨W,r,L1,hL'⟩:=L.costlier
   obtain ⟨n,hn,t,ht,c,K,hc,hK,hT⟩:= diagram F ax h he P hp H (hL'.toPackage.toTableTickets.system) Q hq d N
   let T:= survey S F ax n d; let m(k):= spot (t k)
   obtain ⟨Y,J,V,p,b,a,n₀,hv,hA⟩:= hN n hn.le
   have hi : ∀ᶠ k in atTop, κ k  ≤  t k:= hT.mono fun i hi=>hi.1
   have hμ:= smallness ht hi
   let D:= d+3+2*a+2
   -- at all late k buy with exponent D
   let X:= Desk.Sector B! d
   let F':= Frames.Col X
   let R i:= T (Sample.length i)
   have Ht : ∀ᶠ k in atTop, (Nonempty (Stop C Sample.age Sample.length n₀ m k D)) ∧
     ∃ Y:F'→ₗ[ℂ] C.label d, Nonempty (ReadingAt C S d X (R (m k)) k M Y D) :=by
      filter_upwards [hT, ages H hi, hμ.eventually_ge_atTop n₀,ht.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)),(hat_grows (C:=C) H).eventually_ge_atTop (Real.exp 1)] with k hT hY hn hk hh
      let a':= Sample.age (m k); let e:= engineering (S:=S) M d k; let q:=chol k
      obtain ⟨hT,hV,Y',⟨hr⟩,-,-⟩:=hT
      have hs := C.S.a_pos k; have hX:= touches (hs.trans_le hT) hk
      have hy:= hA _ hn (t k) hX.1 hX.2.1
      have he:= Real.one_le_exp (show (0:ℝ) ≤ 1 by norm_num); have hq :1  ≤  q:=he.trans hh
      have hP: a'^a  ≤  q^(2*a):=by rw [pow_mul]; exact pow_le_pow_left₀ (show 0 ≤ a' from by unfold a' Sample.age;positivity) hY _
      have hQ(i j:ℕ)(h:i  ≤  j):q^i ≤  q^j:=pow_le_pow_right₀ hq h
      have hW: Sample.length (m k)  ≤  κ k*q^4:=by
         have hU:= hX.2.2.trans (mul_le_mul hh hV (by positivity [show 0<t k from hs.trans_le hT]) (by positivity))
         apply hU.trans_eq; unfold q; ring
      refine ⟨⟨hn,hY.trans (hQ 2 _ (by unfold D;omega)), hW.trans (mul_le_mul_of_nonneg_left (hQ 4 _ (by unfold D;omega)) hs.le), (hT.trans hX.2.1).trans (le_mul_of_one_le_right (samples_spacing _).1.le (one_le_pow₀ hq))⟩,Y',⟨⟨fun v=> ?_,fun v=> (hr.norm v).trans (mul_le_mul_of_nonneg_right (hQ _ _ (by unfold D;omega)) (norm_nonneg _)),fun v=>?_⟩⟩⟩
      · refine ((hy _).2.trans ?_)
        apply (mul_le_mul hP (hr.look v) (Real.sqrt_nonneg _) (by positivity)).trans
        change q^(2*a)*(q^(d+3)*mass C _ v)  ≤  _; rw [←mul_assoc,←pow_add]; exact mul_le_mul_of_nonneg_right (hQ _ _ (by unfold D; omega)) (mass_nonneg ..)
      apply (hr.price v).trans
      have he:= (hy (e (Y' v))).1; let U:= R (m k) (e (Y' v)); change T (t k) (e (Y' v))  ≤  _*U at he
      apply (mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_right hP (Real.sqrt_nonneg _))) (by positivity : 0 ≤  q^(d+3))).trans
      change q^(d+3)*(q^(2*a)*U) ≤  q^D*U; rw [← mul_assoc,← pow_add]; exact mul_le_mul_of_nonneg_right (hQ _ _ (by unfold D; omega)) (Real.sqrt_nonneg _)
   obtain ⟨K,hK⟩:=eventually_atTop.mp Ht
   choose! Y' hy using fun k : ℕ=> fun h:K ≤ k => (hK k h).2
   have hf:∀ᶠ k in atTop,Nonempty (ReadingAt C S d X (R (m k)) k M (Y' k) D):=(eventually_ge_atTop K).mono fun i hi=> hy i hi
   exact ⟨march_right hv m (Ht.mono fun i hi=>hi.1) Y' hf H,fun w=>march_row hv m (Ht.mono fun i hi=>hi.1) Y' hf H w (fun i _ z=> Desk.fits Q hq d i z)⟩
omit h he [ϕ.NeBot] in
lemma reading_sharp (Q:Prescription B!)(hq:Q.Coherent) (hx:∀ d,4 ≤ d→ March F ax Q hq d):
    (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤f.fuse∧OPE.Log.MatrixTicket S B! ϕ) ∧ LogTrace F Q:=by
   have hp := matrix_ticket_from_limits H S B! f F.room.cutoff (fun b x hb M hM=> by
     have hc(d):RightPrice C S M d ∧ ∀ i,RowPrice C S B! M d i:= by
        rcases lt_or_ge d 4 with hc|hc
        · exact ⟨low_right_price H hM S d hc,fun w=>low_row_price H hM S B! F.room.kernel.laws F.phase.transport.injection d w hc⟩
        exact applyAt F ax hM hb P hp H L Q hq d (hx d hc)
     exact ⟨fun i=>(hc i).1,fun i=>(hc i).2⟩)
   obtain ⟨q,hQ,hJ,hw⟩:=hp
   exact ⟨⟨_,hQ,hJ,hw⟩,tickets_suffice F L hJ hw hq⟩
end YM.RG12.Arche.Drives
