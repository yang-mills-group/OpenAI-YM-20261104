import YM.FVA2.Gen.EdgeLight
import YM.FVA2.Press.Panels
/-! # Survey sampling reads through h directly and strongly on the nonlinear smooth connection

 Real transport input first; step gauge exact.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision Source Wilson Drops Work G05 Bid
open Press XSpace
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge}{A: Sky G}{J:Labels.Jet G}{H:Hol G}{x:E4}{i:Axis}{k d:ℕ}(S:XSpace.Survey G H d)
local notation "P"=> E4
local notation "U"=> G.mat
local notation "Λ"=> G.lieExp
variable {a:E}{q p:E→CoverConfig G}
/-- read smooth field kernel using only (local) links in knots. Vacuum anchor. -/
abbrev coverSeed (G:Gauge)(E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E](a:E)(p:E→CoverConfig G): Prop:= p a=1 ∧ ∀ i:Edge Cover, ContDiffAt ℝ ∞ (fun t:E=> G.mat (p t i)) a
private def pinch (p:E→CoverConfig G)(x:E): Press.tilt S:= fun u=> G.plog (U (p x u.val))
private lemma pinch_d (hp:coverSeed G E a p): ContDiffAt ℝ ∞ (pinch S p) a:= contDiffAt_pi.mpr (fun i=> by
    obtain hx:= hp.2 i.val; refine ContDiffAt.comp (g:=G.plog) _ ?_ hx; rw [show p a i.val=1 from congr_fun hp.1 _ ]; exact G.plog_diff.of_le le_top )
private lemma fit_seed (hp:coverSeed G E a p): ∀ᶠ x:E in 𝓝 a, mapped S.looks (p x)=Press.lamp S ( pinch S p x ):= by
    refine ( (Filter.eventually_all (p:=fun (i:Local S) x=> p x i.val=Λ ( pinch S p x i ))).mpr ?_ ).mono (fun x hv=> reception S _ hv); intro i
    have hx:ContinuousAt (fun t:E=> p t i.val) a:=( G.continuous_mat.isClosedEmbedding G.mat_injective ).isEmbedding.tendsto_nhds_iff.mpr ( hp.2 i.val ).continuousAt.tendsto
    have he:Tendsto (fun t:E=> p t i.val) (𝓝 a) (𝓝 1):= by convert hx.tendsto using 2; exact ( congr_fun hp.1 _ ).symm
    exact ( he.eventually G.plog_right ).mono (fun x hv=> hv.symm )
lemma cover_c (hp:coverSeed G E a p): ContDiffAt ℝ ∞ ( S.reading ∘ p ) a:= by
    refine ( S.recover_smooth.of_le (m:=∞) le_top|>.contDiffAt|>.comp a ( ((Press.lamp_smooth S).of_le (m:=∞) le_top).contDiffAt.comp a (pinch_d S hp) ) ).congr_of_eventuallyEq ?_ -- exponent
    filter_upwards [fit_seed S hp] with x hx; exact congr_arg S.recover hx
lemma cover_near {p q:ℝ→CoverConfig G}(hp:coverSeed G ℝ 0 p)(hq:coverSeed G ℝ 0 q)(he:∀ i:Edge Cover,Near k (fun t=> U (p t i)) (fun t=> U (q t i))): Near k (S.reading ∘ p) ( S.reading ∘ q ):=by
    let f(x:Press.tilt S):=S.recover ( Press.lamp S x ); have hf:ContDiff ℝ ∞ f:= ( S.recover_smooth.comp ( Press.lamp_smooth S ) ).of_le le_top
    have hv {p:ℝ→ CoverConfig G}(hp:coverSeed G ℝ 0 p): S.reading∘p=ᶠ[𝓝 0] f ∘ pinch S p:= (fit_seed S hp).mono (fun x hx=> congr_arg S.recover hx); apply ( near_of_ev (hv hp) ).across ( ( Near.vcomp ?_ (pinch_d S hp) ( pinch_d S hq ) hf.contDiffAt ).across ( near_of_ev (hv hq).symm )); refine Near.from_each ?_ (pinch_d S hp) (pinch_d S hq); intro i; exact ( Near.vcomp (ψ:=G.plog) ( he i.val ) ( hp.2 i.val ) ( hq.2 i.val ) ( by rw [show p 0 i.val=1 from congr_fun hp.1 _,G.mat_one]; exact G.plog_diff.of_le le_top ) )
lemma standard : Near d (fun x:ℝ=> S.reading ( H.links d J x )) ( fun h:ℝ=> trunk d (scaleJet J h) ):= by
   letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
   -- adapt Work.G05.recovery_projects direct for all coordinates.
   let A(h:ℝ):= trunk d (scaleJet J h); let W:=bring H d S.looks ∘ A
   have hA: ContDiffAt ℝ d A 0:= by
     have T {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](j:ℕ)(c:F): ContDiffAt ℝ d (fun x:ℝ=> x^j • c) 0:= ContDiffAt.smul (contDiffAt_id.pow _) contDiffAt_const; exact contDiffAt_pi.mpr (fun i=> T (i.val+2) (J i.val))
   have h0:A 0=0:=by funext i; simp [A,trunk,scaleJet]
   have hW:ContDiffAt ℝ d W 0:= by refine ( ( show ContDiffAt ℝ d (bring H d S.looks) (A 0) from ?_ ).comp 0 hA ); rw [h0]; exact contDiffAt_pi.mpr (fun i=> ( ( peg H d ).shot ( S.looks i )|>.contDiffAt ).of_le le_top )
   have hz : W 0=0:= by unfold W; rw [ comp_apply,h0 ]; exact funext fun i=> takes_zero ..
   have hw(x): mapped S.looks (H.links d J x)=W x:= by rw [Drops.scales H]; rfl
   have ht:Tendsto A (𝓝 0) (𝓝 0):=by simpa only [h0] using hA.continuousAt.tendsto
   have hg : S.sees ∘ W=ᶠ[𝓝 0] A:=ht.eventually S.kit.2.2.1
   have hc:ContDiffAt ℝ d S.sees 0:= S.kit.1.contDiffAt.of_le le_top
   intro k hk; rw [show (fun x:ℝ=>S.reading _)= S.recover ∘ W from funext fun x=> congrArg S.recover (hw x), ← show iteratedDeriv k ( S.sees ∘ W ) 0=_ from hg.iteratedDeriv_eq k ]; -- inner
   unfold iteratedDeriv; rw [jets_comp hW hW (S.recover_smooth.contDiffAt.of_le le_top) ( by rw [hz]; exact hc ) rfl (fun _ _=> rfl) ?_ k hk ]; rw [hz]; exact blockTaylor_jets hc
-- relation to full Jets - doesn't require root invariance.
-- world convention
variable {p:Breeze G}
private lemma fpotential (J:Jet G): Fluid (Source.potential d J):=by
    intro i; exact ContDiff.sum (fun j _=> Tensor.diag_smooth ..)
private lemma cOnes (H:Hol G)(J:Jet G): Air (fun t l=> H.flow d J t l) (Source.potential d J):= fun l t=> H.solves d J t l
lemma air_cover (h: Air p A)(hf:Fluid A): coverSeed G ℝ 0 ( bookend p ):= by
    refine ⟨ ?_,fun i=> ( ( h i ).smooth ( barC hf i ) ).contDiffAt ⟩; funext i; apply G.mat_injective; exact ( (h i).equip (barC hf i) (fun t=> (zero_smul ℝ _))).base
private lemma projected (x:E4)(i:Axis)(h:Radials A J)(hf:Fluid A)(hp:Silent A): Near (d-1) (fun t:ℝ=> (Source.potential d J) i (t • x)) (fun t:ℝ=> A i (t • x)):= by
 intro k hk; let f(t:ℝ):= t • x; let z:=J; cases k with
 | zero=> simp only [ iteratedDeriv_zero,zero_smul,potential,null_centre hf hp ]; refine Finset.sum_eq_zero (fun j hj=>?_); exact ContinuousMultilinearMap.map_zero ( ( J j ).val i )
 | succ k=>
    have hm:k+1<d:=by omega
    unfold potential; simp_rw [Labels.Taylor.value_hom]; rw [iteratedDeriv_fun_sum (f:= fun j:ℕ=> fun t:ℝ=> t^(j+1) • (J j).value i x) (fun j _=> ContDiffAt.smul (contDiffAt_id.pow _) contDiffAt_const), Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega)) (fun y hy hc=> ?_)]; rw [ lift_symbol, if_pos rfl, ( knows hf hp J ).mpr h, smul_inv_smul₀ (by positivity: ( (k+1).factorial:ℝ ) ≠ 0) ]; rw [ lift_symbol, if_neg (by omega) ]
theorem rung (h:Air p A)(hA:Fluid A)(he: Radials A J): Near d (S.reading ∘ bookend p) (fun t=> trunk d ( scaleJet J t )):=by
    obtain ⟨k,hk⟩:= meets_real ( cCircle hA ); obtain ⟨u,hu,h0,hf,hS⟩:= still_τ hk hA; obtain ⟨q,hq⟩:= skyway_air hf; have hv(t:ℝ): S.reading (bookend p t)= S.reading (bookend q t):= by rw [ Edge_gau h hq hu,S.reading_gauge, show groundC t u 0=1 from ?_ ]; symm; funext i; unfold Cast; apply Labels.Taylor.value_ext; funext j x; simp only [ Labels.Taylor.paint_value,G.adjoint_one ]; rw [groundC, show G03.castPos 0=0 from (by ext i; simp [G03.castPos]), smul_zero,h0] -- rfl cast?
    rw [show S.reading ∘ bookend p=S.reading ∘ bookend q from funext hv]; refine Near.across (q:=S.reading∘ (fun t:ℝ=> H.links d J t)) ( cover_near S (air_cover hq hf ) (?air) ?_ ) ( standard S )
    · exact air_cover ( cOnes H J ) ( fpotential J ) -- signature S not needed?
    intro i; let F(t:ℝ)(x:Edge Cover):= H.flow d J t x; let l := slides (skyturn u A) i; let L := slides ( Source.potential d J ) i; have hC: Engage 0 ( enter G L ) (fun t v=> U ( F t i v )) := ( cOnes H J i ).equip ( barC (fpotential J) i ) ( fun t=>zero_smul .. ); have hh: Engage 0 ( enter G l ) ( fun t v=> U (q t i v ) ):= ( hq i ).equip ( barC hf i ) (fun t=> zero_smul ..); apply ( hC.near hh (n:=d) ?_ ).turn -- assign
    intro t; -- comp from polynomial powers
    let x:= spot i t; have hx: Near d (fun a:ℝ=> L (a,t)) (fun a=> l (a,t)):= ( ( projected (d:=d) x i.2 ( ( keeps hA hu h0 ).mpr he ) hf hS ).weight ( ( ( fpotential J i.2 ).comp (f:=fun t:ℝ=> t • x) ( contDiff_id.smul contDiff_const ) ).contDiffAt ) ( ( ( hf i.2 ).comp (f:=fun t:ℝ=> t • x) ( contDiff_id.smul contDiff_const ) ).contDiffAt ) ).low (by omega)
    exact hx.vcomp (hp:= ((barC ( A:= Source.potential d J ) ( fpotential J ) i ).comp (f:=fun x:ℝ=>(x,t)) (contDiff_id.prodMk contDiff_const)).contDiffAt ) (hq:= ((barC hf i).comp (f:=fun x:ℝ=>(x,t)) (contDiff_id.prodMk contDiff_const)).contDiffAt ) G.colorMat.toContinuousLinearMap.contDiff.contDiffAt
end YM.FVA2.Gen
