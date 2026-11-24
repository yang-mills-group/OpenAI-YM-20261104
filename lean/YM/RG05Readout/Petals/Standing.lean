import YM.RG05Readout.Petals.Pan
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
/-!
# Manifest erasures under multi-charge. Price semantics additive.
 General vectors x only dollar (CAN grow) paid via normalization first in next file. Need actual valuation for residual discrepancy: witness is genuine Stencil bought on SAME extraction, not field projected by FREE. Supports price works before any normalization inside correlation tests. -/
open Dash Extraction Extraction.Lease UVExt -- Avoid `Slots` ambiguity namespace Petals.Slots
/-!
# Detector add-ons for reaching U.Spans on common ordered extraction
-/
open Kernel Bay
local notation "T'"=> C.S.a
local notation "t₀"=> C.S.a N
local notation "Z"=> C.side N p
section
variable (L':Poem C b) (x:Leafage C d)
local notation "I"=> Fin L'.n
local notation "K"=> Fin (L'.n+1)
variable (P:Extraction.Lease.Trial C)
local notation "F"=> C.O N p
local notation "r"=> L'.opening

lemma stander (u:Body)(he:∀ i,Continuous (P N p i)): Continuous (specimen u P N p):= by
    unfold specimen; apply Continuous.const_smul; simp_rw [Finset.sum_fn]; apply continuous_finsetSum; exact fun _ _=> (he _).const_smul _
lemma minting (u:Body) : Continuous (fieldC C m N p d (x (N,p)) u):=by
    unfold fieldC; apply Continuous.const_smul; simp_rw [Finset.sum_fn]; apply continuous_finsetSum; intro i _; change Continuous ((entrance C _ N p (x (N,p)) 0 (restricted C N p i u)) ∘ Lattice.pull 1 i); exact Continuous.comp (show Continuous (entrance C _ N p (x (N,p)) 0 (restricted C N p i u)) from Harvest.precinct_t (x (N,p)) (p:=p) (N:=N) _) (continuous_pull _ _) -- editing

local notation "W!"=> Wave Unit
def incline (p:Body): Wave Unit:=Pulse.joint Finset.univ (fun _:Unit=> p)
lemma read_incl (g:Body)(v:Config G Z): Petals.sheet (incline g) C (fun _ :Unit=> P) N p v=specimen g P N p v:=by
    unfold sheet specimen; let t:(Site Z)≃ (Unit→Site Z):=(Equiv.piUnique (fun _ :Unit=> Site Z)).symm; rw [← Equiv.sum_comp t]; simp_rw [Finset.prod_const, Finset.card_univ,Fintype.card_unique, pow_one, Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; apply congr_arg; apply Finset.sum_congr rfl; intro i hi; unfold incline Pulse.joint; change (∏ u:Unit,_)*(∏ u:Unit, _)= _; simp_rw [Fintype.prod_unique]; rfl
lemma together_one (g:Body) : multi C m N p (fun _ : Unit=> d) (fun _=> x (N,p)) (incline g)=fieldC C m N p d (x (N,p)) g:=by unfold incline; rw [from_fields]; funext v; simp_rw [Fintype.prod_unique]
-- Body Tall global availability
open Nuclear
lemma tall_any {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{u:Complexion V}(hx:HasCompactSupport u.val) (d:ℕ) : ∃ B:ℝ,0< B∧ Nuclear.Tall u d 1 B:=by
   have hv(i:Fin (d+1)):= (lit u i.val|>.continuous_iteratedFDeriv (show ((i.val:WithTop ℕ∞)) ≤ i.val from le_rfl)).bounded_above_of_compact_support (hx.iteratedFDeriv i.val)
   choose Q hQ using hv; obtain ⟨a,ha,hb⟩:= ((eventually_gt_atTop (0:ℝ)).and (eventually_all.mpr (fun i=>eventually_ge_atTop (Q i)))).exists; refine ⟨a,ha,fun i hi v=>?_⟩; rw [one_pow,one_mul]; exact (hQ ⟨_,i.lt_succ_self.trans_le (Nat.succ_le_succ hi)⟩ v).trans (hb _)
lemma packet_one (u:Body)(B':ℝ)(hB:0≤B')(hp:∀ x∈tsupport u.val, ‖x‖≤B'):HasCompactSupport (incline u).val :=by
    apply (isCompact_closedBall 0 B').of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ Metric.isClosed_closedBall); intro x hx
    apply Metric.mem_closedBall.mpr; rw [dist_zero_right]; apply (pi_norm_le_iff_of_nonneg hB).mpr; rintro ⟨⟩; apply hp _ (subset_closure ?_); change u.val (x ())≠0; change (∏ i:Unit,u.val (x i)) ≠0 at hx; simpa using hx
variable {w ξ} (Y:OPE.Package C w ξ D) (hG:G.Simple) (hx:Slow C f x)
local notation "F'"=> code m k x
local notation "g!"=> (L'|>.opening)
-- FD exact h.Spectator pledge only if k pays also this finite Poem n
noncomputable def craving (d:ℕ):ℕ:= d+ (∑ i:Fin L'.n,(L'.token i).1)
include h Y hG hx
lemma with_pledge (he: craving L' d≤ k) : Tendsto (fun z:ℕ×ℕ=> Bid.targetB F' L'.sight z.1 z.2 - preamble L' z.1 z.2 (fieldC C m z.1 z.2 d (x z) g!)) f.fuse (𝓝 0):=by
    let u:=(g!); let t:= (C.S.a b/8); have hp:0<t:= div_pos (C.S.a_pos _) (by norm_num)
    let G':= incline u; have hv(i)(hi:i∈tsupport u.val):‖i‖≤t:= (le_trans (le_of_eq (dist_zero_right i).symm) (Metric.mem_closedBall.mp (Poem.opening_there L' hi))).trans (show C.S.a b/16≤t from by unfold t; have h:= C.S.a_pos b; linarith)
    obtain ⟨A,hA,hU⟩:= tall_any (packet_one u t hp.le hv) (k+1)
    have hB(y : Cloud Unit)(hz:y∈Function.support G'.val): ‖y‖≤t:=by change (∏ i:Unit,u.val (y i)) ≠0 at hz; rw [Fintype.prod_unique] at hz; exact (pi_norm_le_iff_of_nonneg hp.le).mpr (by rintro ⟨⟩; exact hv _ (subset_closure hz))
    have hh:d≤k:= by unfold craving at *; omega
    obtain ⟨c,hc,hL,hc'⟩:= all_envelopes (m:=m) h (fun _ :Unit=> d) (fun _=> x) hG (fun _=>hx) ((craving L' 0)+1) (k:=k) (by simpa) (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_smul]; unfold craving at *;omega) A t hA.le
    obtain ⟨a,ha,hM,ha'⟩:= loose h L' (f:=f) hG
    let w': Cutoffs → ℝ:= fun i=> a i*c i; have hw:=hM.mul hL; let z(j:Cutoffs):= fieldC C m j.1 j.2 d (x j) g!; let F₁: ℕ × ℕ →ℂ:= fun j=> Bid.targetB (code m k x) L'.sight j.1 j.2 - preamble L' j.1 j.2 (z j)
    have hX : Slow C f (fun i:Cutoffs=> ((C.S.a i.1:ℂ)^(d-d))⁻¹ • x i):= by simpa using hx
    have hPr:= ((bids h x Y hG le_rfl hX (m:=m) (k:=k)).1).root
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg (F₁ i)) ?_ (flight_lands (C:=C) (ε:=1/2) (by positivity)))
    have hD:= hw.sink (show (1/2:ℝ)<1 from by norm_num)
    filter_upwards [hD,hc',ha'] with i hi hj ht; rcases i with ⟨n',p'⟩; let g:=code m k x; let t':Goods G (C.side n' p'):= specimen u g n' p'; let X'':= z (n',p'); have hx':Continuous t':= stander g u (hPr n' p'); have hU':Continuous X'':= minting x u
    change ‖Bid.targetB (code m k x) L'.sight n' p'-preamble L' n' p' X''‖ ≤ _; rw [marked L' _ (hPr n' p'), ← onward_minus L' t' X'' hx' hU']; have hb(B:Config G (C.side n' p')): ‖(t'-X'') B‖ ≤ ((C.S.a n')^(craving L' 0+1))*c (n',p'):=by
          have h:= hj G' (fun x=> by simpa using hU (k+1) le_rfl x) hB B; rw [show sheet G' C _ (n',p').1 (n',p').2 B=t' B from read_incl g u B,show multi C m (n',p').1 (n',p').2 _ _ G' B=X'' B from congr_fun (together_one (C:=C) x u) B] at h;exact h
    apply le_trans (ht _ _ (hx'.sub hU') hb) (le_trans (le_of_eq ?_) hi); change _=w' _*flight C (-1) (n',p'); unfold flight; dsimp only; rw [Schedule.scale, Real.log_inv,neg_one_mul,neg_neg, Real.exp_log (C.S.a_pos n')]; unfold w' craving; rw [zero_add,pow_succ]; have ht:= C.S.a_pos n'; field_simp
end
end YM.RG05Readout.Petals
