import YM.Qlocal.Quipu.Brands
import YM.Qlocal.Feud.Course
/-!
 # Restoring the frame pricing. Genuine availability from Witness.Fk, not fixed-P.DAT.Note.FVA accuracy along Clock claimed later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j m i q r n:ℕ} {c f :Side}{S:StepData c f} {b a α δ t:ℝ}
open Quipu.Sonnet
namespace Peak
open Quipu Quipu.Sonnet Tern
open Eluder Eluder.Incline Incline.Bookworm
variable {ι σ:Type*}{V:Type}[DecidableEq V]{Z:Marker.Census V}
open Cider Quipu.Sonnet.Tern.Stanza Bind Horn
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock Aux.Name Presented Poll
open Tensor Fire
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Ker Ker.Start Kinetic.Port Kinetic
section scope
variable (A:Tale Z G) (s:Senses Z) (o:V→Site c) (h:A.Allows α b)(hα:0<α)
local notation "Y"=> rule (Coarse G) c
local notation "X"=> Apex c G
local notation "F"=>A.markℓ (Anthem.statement A) o s
local notation "T"=> exteriorL G c
local notation "Θ"=> Anthem.grasp0 A o s
local notation "d"=> A.boom s
include h hα
lemma frame_match (u:X) (i:ℕ): Radial.jet (Peak.horizon (A.markℓ (Anthem.statement A) o s)) (A.boom s+i) (1,u)=Anthem.grasp0 A o s i ((exteriorL G c).symm u):= by
 let f:=(A.markℓ (Anthem.statement A) o s); let V:=Comparison.RG02.Bulk.projected f; let L:=(ContinuousLinearMap.id ℝ ℝ).prodMap (tint G (Exterior.Body 1 c)).toContinuousLinearMap; have hv: ContDiffAt ℝ ω V 0:= (A.quartile s o h hα (Anthem.statement A)).zeroAt.smooth; rw [Nat.add_comm]; unfold Anthem.grasp0; change Comparison.RG02.Assembly.jet (V ∘ L) _ _= Comparison.RG02.Assembly.jet V _ (1, ports G c ((T).symm u)); rw [jet_continuous_right _ (hv.of_le le_top), ports, ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.apply_symm_apply]; rfl
omit h hα
lemma exit_cost (p:X): ‖(exteriorL G c).symm p‖≤‖p‖ := by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro i; exact norm_le_pi_norm p ((Primitives.TwoWave.RealSlice.outsider G c) i)
end scope
section certificate
variable (Z0 : Catch.Clock ι) {P:Patch}{K:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F₀:Uniform.Before G v.width v.paths P.J K (k+3+3)}
variable (W:ι→ Aux.Name G P K u κ v (k+3) F₀) (d:ι→ℝ)(x:∀ i,(W i).X)
variable (g:V→ℕ) (o:∀ i:ι,V→Site (W i).c) (s:Senses Z) (A:ι→Stanza Z G g m)(N:ℕ)
local notation "L"=>Z0.rail
local notation "U"=>Stanza.son
set_option quotPrecheck false
local notation "P[" i "]"=> Stanza.son (A i) N
local notation "snap"=> scene W g m N A (fun i=> Anthem.statement (Stanza.son (A i) N)) s o
-- either Price estimated in k or stronger not chosen `auth threshold λ`. relative cM per j limit.Rest.Cull. Universes Type Clip.
variable (Y:∀ i,(W i).X→ Word ℝ) (Gv:ι→ℝ)
-- weight C can vary with j in theorem
local notation "rankm"=> Lagger.dues g s.val
local notation "w"=> fun i:ι=> (W i).Θ
local notation "Γ"=> Catch.Cover Z0 j
local notation "Ψ"=> Peak.token W snap
local notation "F[" i "," j "]"=> Anthem.grasp0 (P[i]) (o i) s j
local notation "X[" i "]"=> (W i).X
local notation "R_"=> rule (Coarse G)
local notation "Pℓ[u]"=> False
local notation "C[" i "]"=> rule (Coarse G) (W i).c
-- field *at θ*
local notation "ε"=>fun i=> (d i)⁻¹
abbrev frozen (j:ℕ)(q:ι): rule (Coarse G) (W q).c → ℝ:= fun vY=> Y q ((W q).Θ • ((exteriorL G (W q).c) vY)) j
def Expectations (j:ℕ)(i:ι): Prop := Prices (rankm + j) (Gv i) (Anthem.grasp0 (P[i]) (o i) s j - frozen W Y j i)
variable (hT:Aux.Name.Proper W Z0)(K_σ:ι→ℝ) (ha:∀ i, ((A i).son N).Allows α (K_σ i))(hz:0<α) (h0:∀ᶠ i in Z0.rail,0<d i)(hK:Z0.Meter d (-(1/2:ℝ)))(hx:Z0.Meter (fun i=> ‖x i‖) (-(1/2:ℝ)))(hG: Z0.Meter Gv δ)(he:∀ᶠ i in Z0.rail,Expectations W g o s A N Y Gv q i)
local notation "f"=> fun i (y:X[i])=> Peak.token W snap rankm i y q-Y i y q
include hT hK hx h0 hG ha hz he
lemma income_w : Catch.Cover Z0 j δ ε (fun i (y:(W i).X)=> Peak.token W snap (Lagger.dues g s.val) i y q-Y i y q) x := by
 let P0:= rankm; let H0 i:= exteriorL G (W i).c; let L0 i: X[i] →L[ℝ] rule (Coarse G) (W i).c:= (H0 i).symm.toContinuousLinearMap ∘L ((w i)⁻¹ • ContinuousLinearMap.id ℝ _); let F' i:= F[i,q] - frozen W Y q i; have h(i): f i= (F' i)∘ L0 i:= by
   ext1 v; change Radial.jet (Peak.horizon ((P[i]).markℓ (Anthem.statement (P[i])) (o i) s)) ((P[i]).boom s+q) (1,(w i)⁻¹ • v)-_= _; rw [show Radial.jet _ _ _=Anthem.grasp0 (P[i]) (o i) s q (L0 i v) from frame_match _ s (o i) (ha i) hz ((w i)⁻¹ • v) q]; unfold Function.comp F'; rw [Pi.sub_apply]; apply congr_arg; change _=Y i ((w i) • (H0 i) ((H0 i).symm ((w i)⁻¹ • v))) q; rw [ContinuousLinearEquiv.apply_symm_apply,smul_smul,mul_inv_cancel₀ (show w i ≠0 from (W i).Θp.ne'),one_smul]
 let x0 i := closedBall (x i) (d i); let T:= Z0.book x0; let p {i:ι} (v:X[i]):= (x0 i); let H:=fun i:(Σ i:ι,{v:X[i]//v∈x0 i})=> i.2.1; let y:=Z0.bookF x0
 have hY:T.Meter (fun i=> ‖H i‖) (-(1/2:ℝ)):= Aux.Name.aux_burden hx hK
 have hv:T.Meter (fun i=> ‖L0 i.1 (H i)‖) 0:=by
    apply ((( (hT.meter W|>.2.pays Sigma.fst y)).mul hY).weak ?_).smaller; swap; · norm_num
    filter_upwards with i; rw [abs_of_nonneg (norm_nonneg _)]; change ‖(H0 i.1).symm ((w i.1)⁻¹ • (H i))‖≤ _; apply le_trans (exit_cost _) _; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (show 0<w i.1 from (W i.1).Θp).le)]; exact le_abs_self _
 have he':= y.tends.eventually he; refine Warp.action (n:=P0+q) _ j (he.mono (fun i hi=>?_)) ?_ h0
 · change Prices _ _ _ at hi; change Rank _ _ (f i); rw [h]; exact hi.2.1.lead (L0 i)
 refine (Meter.smaller (((hG.pays Sigma.fst y).mul (((Meter.const T 1).add hv).pow (P0+q))).weak (by simp)) ?_ ); filter_upwards [he'] with i hi; change Prices _ _ _ at hi; change |f i.1 (H i)| ≤ _; rw [h]; exact hi.2.2 (L0 i.1 (H i))|>.trans (le_abs_self _)
-- sum passports over q≤r separate h.Frame-Price predicate. imput.React.Body convergence and powers not same ages δ.Clock.Mill.R.
end certificate
end Peak
end YM.Qlocal.Feud
