import YM.RegulatorIR.Oracle.Stem

/-! Full affine prediction turned from ungauged Count. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p: Side} {L:Side} {α σ:ℝ}(P:Patch)(H:KernelChoices)
def chordN (u: Long G.ColorIndex): Gain.Point G := (u.1.1,u.2)
def ledN (u: Long G.ColorIndex) : Gain.Point G:= (u.1.1+step u.1.2,u.2)
def career (G:Gauge)(x: Long G.ColorIndex) : Gain.Point G→₀ ℝ:= Finsupp.single (chordN x) (1:ℝ)-Finsupp.single (ledN x) (1:ℝ)
-- module path opens conflicting RegulatorIR vs Precision

lemma movingD (G:Gauge)(P:Patch):Albedo (blockQ G P.L) (gardens P G) (finer (career G)):=by
 intro x y d; rw [strut]; unfold finer career; rw [Finsupp.sub_apply,Finsupp.sub_apply]
 have hp: chordN (motionsQ x (P.L.val • d))=(gardens P G).shiftB d (chordN x):= Eq.symm (c_shift ..)
 have hz: ledN (motionsQ x (P.L.val • d))=(gardens P G).shiftB d (ledN x):=by rw [c_shift];unfold ledN motionsQ; simp [add_assoc]
 rw [hp,hz]; simp only [Finsupp.single_apply,(gardens P G|>.shiftB d).injective.eq_iff]
lemma gained (G:Gauge) (U: Layer (Long G.ColorIndex) (Long G.ColorIndex)) (R:RegulatorIR.Gain.Bride G) : RegulatorIR.Gain.valve U R = U + lap (finer (career G)) R:=by
 funext i j; change _+ (_-_) = _+ ∑'k,(career G i) k*R k j; rw [tsum_eq_sum (s:=(career G i).support)];
 · rw [show (∑ k∈(career G i).support,(career G i) k*R k j)=_ from (rfl : _=Quadratic.combo (fun k=>R k j) (career G i))]; simp [career,Quadratic.combo]; rfl
 intro k hk; rw [Finsupp.notMem_support_iff.mp hk,zero_mul]
variable (R:Cross P.L (TypeFace 1) (TypeFace 1))(G:Gauge)
lemma placates :Albedo (blockQ G P.L) (linksQ G) (projectionQ P H R G):=by
 unfold projectionQ; rw [gained]; exact (albedoX P R G).add ((movingD G P).lap (albedoQ P H R G))
lemma funded (σ:ℝ):FundE (blockQ G P.L) (gardens P G) σ (finer (career G)):= FundE.bill_s (movingD G P) (fun i=>(career G i).hasFiniteSupport) σ
lemma overrides (h:R.strip σ α)(hp:0≤σ)(he:0≤α) : FundE (blockQ G P.L) (linksQ G) σ (projectionQ P H R G):=by
 unfold projectionQ; rw [gained]
 have hv:= FundE.forw (funded P G σ) (phiE P H R G h hp he) hp; obtain ⟨g,hg,hc,h'⟩:= hv; obtain ⟨c,hq,hk,H⟩:= fond (blockQ G P.L) (linksQ G) _ (adult_price G P R h he)
 exact ⟨c+g,by finiteness,hk.add hc,H.add h'⟩
set_option maxHeartbeats 400000 in
lemma projRates (n:Side) (h:R.strip σ α)(hp:0≤σ)(he:0≤α):
 ledgerRow (blockQ G P.L) (linksQ G) (projectionQ P H R G) n=tensor G (Precision.extracted (avenue P H n) (stemF P n) (installed (tileB P.L n) R)):=by
 let X:=blockQ G P.L;let Y:=linksQ G;let V:= ruling P G R;let S:=avenue P H n
 have hc: Billed (phiQ P H R G):= ((phiE P H R G h hp he).buys hp).1
 have ht : Billed (finer (career G)):= ((funded P G 0).buys le_rfl).1
 unfold projectionQ; rw [gained,Ledger.add _ _ _ ?_ (ht.lap hc), Ledger.lap X (gardens P G) Y n ht hc (albedoQ P H R G)]
 swap; exact ((fond X Y _ (adult_price G P R h he)).buys hp).1
 apply matrixQ; intro v; ext1 i
 obtain ⟨⟨⟨x,a⟩,j⟩,rfl⟩ := (show Surjective (X.swrap n) from fun i=>⟨_,X.both _ i⟩) i
 rw [seatV]; rw [add_mulVec,← Matrix.mulVec_mulVec,Pi.add_apply,cargo_of _ _ (gardens P G) _ n (career G) (movingD G P)]
 let F:= installed (tileB P.L n) R
 let Q:= ledgerRow (gardens P G) (linksQ G) (phiQ P H R G) n
 let x':= wrap (n*P.L) x
 rw [show X.swrap n ((x,a),j)=(x',coord a,j) from v_loc ..]
 change component (tensor G F*ᵥ v) j (x',coord a)+_= component (tensor G (extracted S (stemF P n) F)*ᵥ v) j (x',coord a)
 rw [FreeResolvent.component_mul,FreeResolvent.component_mul]; unfold Precision.extracted; rw [add_mulVec,← Matrix.mulVec_mulVec,Pi.add_apply, Exterior.d_sites]
 apply congr_arg
 rw [career,_root_.map_sub]; simp only [Quadratic.combo,Finsupp.linearCombination_single,one_smul,Function.comp_apply]
 rw [representative P H R G h hp he,representative P H R G h hp he]; simp only [chordN,ledN, _root_.map_add, wrap_step]; change - (straighten _ _ _ *ᵥ _) _ - (- (straighten _ _ _ *ᵥ _) _) = _; simp only [neg_sub_neg]; rfl
end YM.RegulatorIR.Oracle
