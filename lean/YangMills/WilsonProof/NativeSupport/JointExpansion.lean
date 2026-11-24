import YangMills.WilsonProof.NativeSupport.JointSourceSheets
import YangMills.WilsonProof.NativeSupport.JointSound
import YM.MergeProof.Magma

/-! Calibrated measured regular and forced support sheets, with the exact square-zero expansion of the jointly sampled physical transition. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.SelectedKernel
open Merge Merge.Photo JointLeaves
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (marks : ι→Finset (Bond c)) (test : ι→Bond c→ℝ→ℝ) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0) {y' ex dk:ℝ}(h: Usable M Y χ A marks test rA K dk ex y')
open MergeProof Accent Set GridApprox.Nil
variable (b':V→Site c)(hw:∀ i,GridApprox.Nil.Scoped (A:= {x| b' x∈ (M i).crest.image S.ratio.parent}) (z i)) (rV:V→ℝ)(hV:∀ i,0<rV i)(hx:∀ i, Poly.price rV (z i) ≤ 1) (ho:∀ i,(z i).part B.quiet=0)
include h
open Extra.Trajectories
local notation "a"=> barcode A.activities
local notation "U0"=> Fleece K B z
local notation "f"=> headSheet M Y χ marks test rA B z

def spine (p:Support c)(U:Config G c):= tally (fun i:Y.fragrances=>Y.bookFoot (.inr i)) (headSheet M Y χ marks test rA B z) p U

include hV hx
local notation "Z"=> chain A K B z
local notation "W₀"=> spine M Y χ marks test rA B z
lemma exquisite : Towed rV id (spine M Y χ marks test rA B z) A.p.B dk ex:= towing (fun i:Y.fragrances=> Y.bookFoot (.inr i)) _ (flag_E M Y χ A marks test rA K B z h rV hV hx) hV
variable [Fintype V]
include hw
lemma heavily (i:Box c) : Flow b' i ((chain A K B z) i) A.p.threshold:= by
   let f₀:=Fleece K B z; apply transitK (r:=id) a (river M Y χ A marks test rA K B z h b' hw) (F:=f₀)
   exact fun U=>(Towed.repair (flag_K A K B z rV hV hx h.gas A.p.exponent_pos.le) hV U).2
include ho
variable (borel : ∀ i,∀ b∈marks i,Measurable (test i b))
variable (unit : ∀ i,∀ b∈marks i,∀ e0∈Set.Icc 0 (Push.BetaTransport.linkCap S),‖test i b e0‖≤1)
variable (root : ∀ i,∀ b∈marks i,S.ratio.embed b.1∈(M i).crest)
include borel unit root in
lemma serenade (i:Support c): Burns b' i (W₀ i) A.p.threshold:= by
   haveI : Countable Y.fragrances := by unfold Cash.fragrances Clusters Cash.ThinP; infer_instance
   exact transitE (fun i:Y.fragrances=> Y.bookFoot (.inr i)) (r:=id) (F:=f) (curtain M Y χ A marks test rA K B z h b' hw ho borel unit root) (fun U=>(Towed.repair (flag_E M Y χ A marks test rA K B z h rV hV hx) hV U).2) i
omit hw
omit [Fintype V] in
lemma selfie (U : Config G c) (p:Box c): (chain A K B z p U).part B.quiet= profile A.activities (fun i=> Complex.ofReal ∘ A.activities.K i) p U:=by
   obtain ⟨v,hp,hM⟩:=h.gas.bought
   rw [Merge.Photo.chain,Accent.tally,Poly.share]; apply tsum_congr; intro i; rw [Fleece]; let r U t p:= K t p i.val U; change (sound z (r U)).part _= _; rw [sunset r (hp i.val) z U ho]; unfold r; rw [h.gas.term]; rfl
   exact (Towed.repair (flag_K A K B z rV hV hx h.gas A.p.exponent_pos.le) hV U).2.comp_injective Subtype.val_injective
include hZ
theorem expansion (U : Config G c): given (S:=S) M marks test rA B z U=(Real.exp (A.exponent U):ℂ) • (Poly.pass (∑ i, W₀ i U) * Accent.field (fun p=> chain A K B z p U) (RG.flags A.p.threshold U)):=by
   rw [← acts M Y χ A marks test rA K _ z hZ h ho U]
   have he:=Towed.repair (flag_E M Y χ A marks test rA K B z h rV hV hx) hV U |>.2; let t:=fun i:Y.fragrances=> Y.bookFoot (.inr i)
   have ht : ∑' i, Switch.sound z (SelectedKernel.tones M Y χ marks test rA i U)=∑ i, spine M Y χ marks test rA B z i U:= by have hx:=(border t (p:=fun i=> f i U) he).tsum_eq; rw [tsum_fintype] at hx; exact hx.symm
   let p:= A.activities; let s:= RG.flags A.p.threshold U
   let y:= U0; have hf:= Towed.repair (flag_K A K B z rV hV hx h.gas A.p.exponent_pos.le) hV U
   let P:=A.p
   rw [ht,show (fun p':Box _=> chain _ K _ z p' U)= cram a (fun i=>y i U) from rfl,field_eq a s _ hf.2 (Packets.summable_value _ _ _ hV hf.1)]
   refine congr_arg _ (congr_arg (_*·) (tsum_congr ?_)); intro i; rw [shovel]; exact rfl

end YM.Integration.InletSusceptibility.SelectedKernel
