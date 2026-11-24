import YM.FVA2.Gen.Sampling
import YM.FVA2.Gen.Mender
/-!
 # Choose a repaired family through desired depth for all anchors
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision Source Wilson Drops Work G05 Bid
open Press XSpace
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge}{A: Sky G}{J:Labels.Jet G}{H:Hol G}{x:E4}{i:Axis}{k d n:ℕ}(S:XSpace.Survey G H d){Z:Arc ℝ G}{Q:Vehicle ℝ G}
local notation "P"=> E4
local notation "U"=> G.mat
local notation "Λ"=> G.lieExp
local notation "C"=> G.Color
-- transfer before taking Taylor wrt scaled base anchor
abbrev bill (A:Sky G)(i:Axis)(x:E4×ℝ):= x.2 • A i (x.1+ (x.2/2) • basis i)
def Born (A:Sky G)(Q:Vehicle ℝ G)(i:ℕ): Prop:= ∀ (x:E4)(j:Axis), Near i (fun t=> bill A j (x,t)) (fun t=> alongB Q j (x,t))
lemma billC (h:Fluid A): ContDiff ℝ ∞ ( bill A i ):= ContDiff.smul contDiff_snd ( ( h i ).comp (f:=fun x:P×ℝ=>x.1+ (x.2/2) • basis i) (by fun_prop) )
lemma adjust (A:Sky G)(h:Fluid A)(d:ℕ): ∃ Z:Arc ℝ G, ∃ Q:Vehicle ℝ G, Leads Q Z ∧ Flo Z ∧ Z 0=A ∧ Born A Q (d+1):=by
    induction d with
    | zero=>
        let Z(s:ℝ):= A; have hp: Flo Z:= fun i=> ( h i ).comp contDiff_snd; obtain ⟨Q,hQ⟩:= hp.progress
        refine ⟨ Z,Q,hQ,hp,rfl, fun x i=>?_⟩; obtain ⟨he,hf⟩:= headS hQ hp i x; apply Near.taller; · exact near_first.mpr ((show bill A i (x,0)=0 from zero_smul ℝ _).trans he.symm)
        let f(t:ℝ):= A i (x+(t/2) • basis i); have hx:ContDiff ℝ ∞ f:= ( h i ).comp (f:=fun t:ℝ=> x+(t/2) • basis i) (by fun_prop); change iteratedDeriv (0+1) (fun t:ℝ=> t • f t) _=iteratedDeriv 1 (ribbon Q i x) 0; rw [iter_weight (hx.contDiffAt), iteratedDeriv_zero, iteratedDeriv_one, hf]; unfold f Z; simp
    | succ d ih=>
        obtain ⟨Z,Q,hz,hZ,H0,B⟩:= ih; let k:=d+2; let r:ℝ:= k.factorial
        let D: Sky G:= fun i y=> r⁻¹ • ( iteratedDeriv k (fun t=>bill A i (y,t)) 0 - iteratedDeriv k (ribbon Q i y) 0 ); have hD: Fluid D:= by intro i; exact ( ContDiff.const_smul _ ( ( priced ( p:=bill A i ) ( fun _=> ( billC h ).contDiffAt ) k ).sub ( priced ( p:=alongB Q i ) ( hz.paced hZ i ) k ) ) ); -- smooth
        have hv:= lifted hZ hD d; obtain ⟨R,hR⟩:= hv.progress; refine ⟨ fixZ Z D d,R,hR,hv, ( baseZ Z D d).trans H0, fun x i=>?_⟩; obtain ⟨hu,hK⟩:= step_R hz hR hZ hD i x; apply ( (B x i).across hu.turn ).taller
        have hr:r ≠0:=by unfold r; positivity
        change _-_= r • r⁻¹ • _ at hK; rw [ smul_inv_smul₀ hr ] at hK; exact ( sub_left_inj ..|>.mp hK ).symm -- side check
-- logLink midpoint at scaled lattice
abbrev logQuad (A: Sky G)(t:ℝ)(l:Edge Cover):C:= bill A l.2 (t • G03.castPos l.1,t)
def phaseQ (A:Sky G)(t:ℝ) : CoverConfig G := Λ ∘ logQuad A t
abbrev convoy (Q:Vehicle ℝ G)(t:ℝ): CoverConfig G := bookend ( earth Q t ) t
lemma day_C (h:Fluid A): coverSeed G ℝ 0 ( phaseQ A ):= by
    refine ⟨ funext fun i=> ?_, fun i=> ?_⟩; · unfold phaseQ logQuad bill; dsimp only [comp_apply]; rw [ zero_smul ℝ _, G.mat_lieExp_zero ]; rfl -- which order?
    apply ( ( G.exp_jet.of_le (m:=∞) le_top ).comp (f:=fun t:ℝ=>logQuad A t i) ?_ ).contDiffAt; exact (billC h).comp (f:=fun t:ℝ=>(t • G03.castPos i.1, t) ) (( contDiff_id.smul contDiff_const ).prodMk contDiff_id) -- ω mismatch
lemma readyQ {Q:Vehicle E G}{Z:Arc E G} (h:Leads Q Z)(hp:Flo Z)(x:E): coverSeed G ( E×ℝ ) (x,0) (fun t=> bookend ( earth Q t.1 ) t.2):= ⟨ ( air_cover ( h.air x ) (hp.road x) ).1,fun i=> ( h.safe hp i ).contDiffAt ⟩
-- specialization diag corrects log comparison to include y scaling.
lemma convoy_f (h:Fluid A)(hz:Leads Q Z)(hZ:Flo Z)(hp:Born A Q n): Near n ( S.reading ∘ phaseQ A ) ( S.reading ∘ convoy Q ):=by
    apply cover_near S ( day_C h ); · refine ⟨ ?_,fun i=> ( hz.safe hZ i ).contDiffAt.comp (0:ℝ) (f:=fun t:ℝ=>(t,t)) ( contDiffAt_id.prodMk contDiffAt_id ) ⟩; exact (( readyQ hz hZ 0 ).1)
    intro e; let p(t:ℝ):P:=t • G03.castPos e.1; let D(t:ℝ):= (p t,t); have hD : ContDiffAt ℝ ∞ D 0:= ( contDiffAt_id.smul contDiffAt_const ).prodMk contDiffAt_id
    have h0:p 0=0:= zero_smul ..; let i:= e.2
    have hp0:D 0=((0:P), (0:ℝ)):= Prod.ext h0 rfl; let p':=bill A i; let q':=alongB Q i; obtain ht:= hz.paced hZ i 0; obtain ha:(Near n (p'∘ D) ( q'∘ D )):= ( parameter (fun x=> hp x i) (fun x=> ( billC h ).contDiffAt) ( hz.paced hZ _ ) 0 ).along hp0 hD (billC h).contDiffAt ht; let F(t:ℝ) : G.El:= convoy Q t e; have h₀:F 0=1:= congr_fun (readyQ hz hZ 0 ).1 e; have hf:ContinuousAt F 0:= ( G.continuous_mat.isClosedEmbedding G.mat_injective ).isEmbedding.tendsto_nhds_iff.mpr ( (( hz.safe hZ e ).comp (f:=fun t:ℝ=>(t,t)) ( contDiff_id.prodMk contDiff_id ) ).contDiffAt.continuousAt.tendsto ); have he:Tendsto F (𝓝 0) (𝓝 1):=by simpa only [h₀] using hf.tendsto
    refine ( ha.vcomp ( ( billC h ).contDiffAt.comp _ hD ) ( ( show ContDiffAt ℝ ∞ q' (D 0) from by rw [ hp0 ]; exact ht ).comp _ hD ) ( G.exp_jet.of_le (m:=∞) le_top |>.contDiffAt ) ).across ( near_of_ev ( ( he.eventually G.plog_right ).mono ( fun t ha=> congr_arg U (show _=F t from ha) ) ) )
end YM.FVA2.Gen
