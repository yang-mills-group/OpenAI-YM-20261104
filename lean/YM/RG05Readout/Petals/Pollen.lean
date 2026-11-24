import YM.RG05Readout.Petals.Standing
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Kernel Dash
local notation "i!"=> Cutoffs
local notation "F"=> f.fuse
local notation "Σ!"=> Palette C d
abbrev fastU (S: ∀ (_i:Cutoffs), Address.Emblems C d)(M:i!→ Palette C d)(n:ℕ): Leafage C d:= fun i : Cutoffs=> Many.point (S i) (M i) n i.1
variable (u: ∀ (_i:Cutoffs), Emblems C d)(M:Cutoffs→Palette C d)
-- needs law only on used regulator cutoffs
lemma size_paid (v:Palette C d) : size v ≤ (Fintype.card (Mark C d):ℝ)*‖v‖:= by
    refine (Finset.sum_le_sum (s:=Finset.univ (α:=Mark C d)) (f:=fun i=> ‖val v i‖) (g:=fun _=>‖v‖) fun i _=> (norm_le_pi_norm (v i.fst) i.snd).trans (norm_le_pi_norm _ _)).trans_eq ?_; rw [Finset.sum_const,nsmul_eq_mul, Finset.card_univ]
structure UniformM (f:Extraction.Order)(S: ∀ (_i:Cutoffs), Emblems C d)(b:ℕ) (D:Address.Rail C)(B:ℕ→ℕ→ℝ)(h:C.Makes) :Prop where
   aware:Awake D B b d
   actual : ∀ᶠ i in f.fuse, ∃ W:Sight C d i.2, Spine D B h b i.2 d i.1 W (S i)
-- need slow actual S.inverseCost from same spine.Ref tail to warm.
lemma string_parts {i:ℕ}(ht:b ≤ m)(hk:m ≤ i):stringCost C (ht.trans hk)= stringCost C ht * stringCost C hk:=by
    induction i,hk using Nat.le_induction with
    | base=> rw [string_base,mul_one]
    | succ i hk ih=>rw [string_next hk,string_next (ht.trans hk),ih]; ring
lemma starting (m:ℕ): Slow C f (fun i:i!=> if h:m ≤ i.1 then stringCost C h else 1):=by
   intro ε he
   obtain ⟨j,hj,ha⟩:= ((eventually_ge_atTop m).and (string_paid (C:=C) (half_pos he))).exists
   let s:= stringCost C hj; let z:= Real.exp ((ε/2)*(- (C.S.scale j))); filter_upwards [cost_grows (C:=C) (half_pos he) |>.eventually_ge_atTop (s*z),(cutoff_grows f).eventually_ge_atTop j] with i hi hp
   let t:= C.S.scale i.1; let q:= flight C (ε/2) i; have ht:s*z ≤ q:=hi; rw [dif_pos (hj.trans hp),Real.norm_of_nonneg (zero_le_one.trans (stampCosts _)),string_parts hj hp]; have hw: Real.exp ((ε/2)*(C.S.scale i.1-C.S.scale j))=z*q:=by unfold z q flight; rw [←Real.exp_add]; congr 1;ring
   refine (mul_le_mul_of_nonneg_left (le_trans (ha _ hp) hw.le) (zero_le_one.trans (Many.stampCosts _))).trans ?_; rw [←mul_assoc]; refine (mul_le_mul_of_nonneg_right ht (Real.exp_pos _|>.le)).trans_eq ?_; change q*q =_; rw [show q*q=flight C ((ε/2)+(ε/2)) i from Push.RelayDifference.flight_add ..]; rw [add_halves]
-- bound callable W.Replies at every layout.Lexical.Render
variable (hU: UniformM f u b D B h)(hM:b ≤ m)(c':ℝ)(hB:∀ᶠ i in f.fuse,size (M i)≤ c')
local notation "W₀"=> fastU u M m
include hU hB hM h
lemma onboard : Slow C f (fastU u M m):=by
   apply ((starting (C:=C) (f:=f) m).mul (Slow.const c')).reduce
   filter_upwards [hB,hU.actual,(cutoff_grows f).eventually_ge_atTop m] with i hi hs hp; obtain ⟨V,hV⟩:=hs
   rw [dif_pos hp]; unfold fastU; rw [weave_fine hp]; exact (size_norm _).trans ((hV.inverse_cost hM hp le_rfl (M i)).trans ((mul_le_mul_of_nonneg_left hi (zero_le_one.trans (Many.stampCosts _))).trans (Real.le_norm_self _)))

-- response in standing bank doesn't involve finite manipulation with spectator growth. θ powers
variable {w:Worth}{ζ:ℕ→ℕ} (Y:OPE.Package C w ζ D) (Ys:Storage C D)(hG:G.Simple)(W: CenterPort C f)
variable {j:ℕ} (Qp:Poem C j)
-- depends linearly on test. support(tsupport). height
omit hU hB hM h in
lemma saleOne (N p m d:ℕ)(f:Palette C d)(q:Body)(r:ℂ): fieldC C m N p d f (r • q)=r • fieldC C m N p d f q:=by
   unfold fieldC; rw [smul_comm r (gate C m N d)]; apply congr_arg; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [map_smul]
   let t:= restricted C N p i q; rw [show entrance C d N p f 0 (r • t)= r • entrance C d N p f 0 t from ?_, Records.rot_scalar];rfl
   unfold entrance; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul];rw [smul_assoc,smul_comm r (val f j)]
include Y Ys hG
include W Qp in
lemma tagSize : ∃ S:ℝ, ∀ᶠ i in f.fuse, ‖preamble Qp i.1 i.2 (fieldC C m i.1 i.2 d (W₀ i) (Qp.opening))‖≤ S:=by
   let f' := Qp.opening; have hs: HasCompactSupport f'.val:= (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (Poem.opening_there Qp); let c:=max 1 c'; have hc:0<c:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
   obtain ⟨σ,hσ,hf⟩:= tall_any hs (d+2); let t:ℂ:=σ; let t' := t⁻¹ • f'; have ht:t≠0:=Complex.ofReal_ne_zero.mpr hσ.ne'
   have htS: ∀ x∈tsupport t'.val, ‖x‖≤ C.S.a j/8:=fun x hx=> le_trans ((le_of_eq (dist_zero_right x).symm).trans (Metric.mem_closedBall.mp ((Poem.opening_there Qp) (Nuclear.scaled_support t⁻¹ f' hx)))) (by have hx:= C.S.a_pos j;linarith)
   have hT:Nuclear.Tall (E:=E4) t' (d+2) 1 1:=by
       intro i hi x; rw [show t'.val= t⁻¹ • f'.val from rfl, iteratedFDeriv_const_smul_apply (body_smooth ..|>.contDiffAt), norm_smul]; refine (mul_le_mul_of_nonneg_left (hf i hi _) (norm_nonneg _)).trans ?_; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hσ.le,one_pow,one_mul,one_mul,inv_mul_cancel₀ hσ.ne'] -- check
   obtain ⟨A,hA,hX⟩:= Bay.training h hU.aware Y Ys hG j m hM c hc
   obtain ⟨B,hK,hV⟩:= Bay.leaning h Qp W
   refine ⟨B*(‖t‖*A),?_⟩; filter_upwards [hB,hU.actual,hV,(cutoff_grows _).eventually hX] with i hi hs hp he
   obtain ⟨V,hM'⟩:= hs; obtain ⟨hl,hZ⟩:=he; obtain ⟨hw,hY⟩:= hp; let Z':= Cells.center C.S i.2 hl 0; obtain ⟨hb,hc⟩:= hZ i.2 _ (u i) hM' (M i) (hi.trans (le_max_right ..)) t' htS hT; let Y':= fieldC C m i.1 i.2 d (fastU u M m i) f'; let y':= fieldC C m i.1 i.2 d (fastU u M m i) t'
   have ht': Y'=t • y':=by rw [show y'=t⁻¹ • Y' from saleOne ..,smul_smul, mul_inv_cancel₀ ht,one_smul]
   change ‖preamble Qp i.1 i.2 Y'‖ ≤ _; refine (hY Y' (ht'.symm ▸ hb.scale t)).trans (mul_le_mul_of_nonneg_left ?_ hK)
   rw [ht', Next.Extract.root_smul]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
include W Qp in
lemma funded (hp:craving Qp d ≤ k):∃ S:ℝ,∀ᶠ i:ℕ×ℕ in f.fuse, ‖targetB (code m k W₀) Qp.sight i.1 i.2‖≤S:=by
   obtain ⟨A,hA⟩:= tagSize h u M hU hM c' hB Y Ys hG W Qp
   have ht:= with_pledge (m:=m) h Qp _ Y hG (onboard h u M hU hM c' hB) hp; refine ⟨1 + A,?_⟩
   filter_upwards [hA,ht.norm.eventually (ge_mem_nhds (a:=1) (by rw [norm_zero];norm_num))] with i hi hx; let w:= targetB (code m k W₀) Qp.sight i.1 i.2; let x:= preamble Qp i.1 i.2 (fieldC C m i.1 i.2 d (W₀ i) Qp.opening); change ‖w-x‖ ≤ 1 at hx; change ‖x‖ ≤ A at hi; change ‖w‖≤_; linarith only [norm_sub_norm_le w x,hx,hi]

-- existence project.Any needed horizon reannounce input
variable {v:ℕ}{T S:YM.Table C.book}{R:Dash.Bin S}{E:DiffPlan T}{L₀:ℕ→ YM.Table C.book}(H0: Next.Extract.Base C f S L₀ R T E)(hZ:UVExt.Slots.StrongBin C R f v)
-- realize all FD degrees at ≥one plan threshold at this scale. Their reference projections coalesce.Verified.
include H0 hZ
variable {I':Type}[Fintype I'] {P₀:I'→Poem C j}{C':ℝ} (hI:Proctor C f R j v I' P₀ C') (he:v≤d) (hy:Slow C f (fun i:Cutoffs=> ((C.S.a i.1:ℂ)^(d-v))⁻¹ • fastU u M m i))
include hI he hy
set_option maxHeartbeats 410000 in
lemma favored (hk:∀ i:I', craving (P₀ i) d≤k):∃ V:Rowe C v, (∀ i,(R v).step i (V i)=V i) ∧ Reveals C f (code m k (fastU u M m)) V:=by
   obtain ⟨⟨_,hv,hP⟩,ht⟩:= bids (m:=m) (k:=k) h _ Y hG he hy; exact Banking h H0 hI hZ ht hv (fun i=> funded h u M hU hM c' hB Y Ys hG H0.center (P₀ i) (hk i))
end YM.RG05Readout.Petals
