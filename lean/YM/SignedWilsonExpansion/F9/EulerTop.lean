import YM.SignedWilsonExpansion.F9.Vase
import YangMills.WilsonProof.NativeSupport.YM.XSpace.OnShell
/-!
# Nonlinear seeding of the point palette

Top epoch only (!). Provide real contour against true equation inserts; no
identity asserting the downward histories carry such Ward vertices. That is
handled instead by `stateStep` point solver on the ENTIRE offshell panel.
No truncation of SelfCov. And inclusion at common horizon for *raw* through
input, not assuming higher-horizon stencils coincide with own-cap. Rank
remains discrete. `award` enforces the exact Ward powers including at rank 1.
Visibility & leading projection before any coupling changes.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {n:Side}{h d i k r e j:ℕ}{G:Gauge}{H:Hol G}{P:Pill G}
namespace Maskable
lemma pack {E I:Type*} [NormedAddCommGroup E][NormedSpace ℝ E] {x:I→CoverConfig G→ E}(s:Finset I)(h:∀ i∈s, Maskable (x i)): Maskable fun U=> ∑ i∈s,x i U:=by simp_rw [← Finset.sum_apply]; exact stock h
lemma slot (v:RG.Slot): Maskable (v.eval (G:=G)):= colorAct (cur _ (passageM G ..)) (passageM ..)
lemma read_samples {f: Fin d→RG.Slot}: Maskable (Bid.mapped (G:=G) f):= piM _ fun i=>slot _
lemma bond_euler (e:Edge Cover): Maskable (fun U=>euler (G:=G) U e):= pack _ (fun i _=> (cur (fun U=>WardBin.wheel e (posDir i) U) (passageM ..)).plus (cur (fun U=>WardBin.wheel e (negDir i) U) (passageM ..)))
lemma bond_sample (e:Edge Cover):Maskable (sample (G:=G) e):= colorAct (bond_euler e) (passageM ..)
lemma guess (R:Rays G h H):Maskable R.guess:= (piM _ (fun i=>slot (G:=G) (R.slots i))).applies _ R.read.toContinuousLinearMap.contDiff
lemma gapRay (R:Rays G h H): Maskable R.gap:= (piM (F:=↥R.edg) _ (fun i=>bond_sample (G:=G) i.val)).applies _ R.lifts.contDiff
lemma color_force (R:Rays G h H)(M:Tensor.T (Snap G h) ℂ (r+1)): Maskable (R.force M):=
    ((guess R).applies (Tensor.diagonal M) (Tensor.diag_smooth ..)).diff (((guess R).diff (gapRay R)).applies (Tensor.diagonal M) (Tensor.diag_smooth ..))
private lemma pressField {E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E]{X Y Z:CoverConfig G→E}(hx:Maskable X)(hy:Maskable Y)(hz:Maskable Z)(M:Tensor.T E ℂ r)(i: Fin r): Maskable (fun U=> M (Function.update (phased (X U) (Y U) i.val) i (Z U))):= by
    have hb: ∀ j: Fin r, Maskable (fun U=> Function.update (phased (X U) (Y U) i.val) i (Z U) j):=by
        intro j; by_cases h:j=i; subst j; simp_rw [update_self]; exact hz
        simp_rw [update_of_ne h]; unfold phased; split; exact hx; exact hy
    exact (piM (V:=fun _: Fin r=> E) (fun j U=> _) hb).applies (fun x: Fin r→ E=> M x) M.contDiff
lemma color_coField_at (R:Rays G h H)(M:Tensor.T (Snap G h) ℂ (r+1))(e:R.edg)(a:G.Color):Maskable (fun U=>R.coField M e U a) := by
    let T:=R.guess; let V:=T - R.gap; let S(U:CoverConfig G):= R.pays U e a; have ht: Maskable T:= guess R; have hv: Maskable V:= ht.diff (gapRay R)
    have he: Maskable S:= ((colorAct (flat a) (show Maskable (G.mat ∘ toBond e.val) from passageM ..)).applies (ContinuousLinearMap.single ℝ (fun _:R.edg=>G.Color) e) (ContinuousLinearMap.single ℝ (fun _:R.edg=>G.Color) e).contDiff).applies _ R.lifts.contDiff
    unfold Rays.coField; simp_rw [_root_.sum_apply]; apply pack; intro i _; exact pressField ht hv he M i
lemma color_compress (R:Rays G h H)(M:Tensor.T (Snap G h) ℂ (r+1)): Maskable (R.compression M):=
    pack _ (fun i _=>pack _ fun j _=> displaced i.val _ (color_coField_at R M i (dirs G j)))
end Maskable
namespace Pill
variable {z:Label G h} {S:Finset Cover}
-- Rank-r equation decomposed in two pillars
variable (R:Rays G h H)(M:Tensor.T (Snap G h) ℂ (r+1)) (f:R.FitsAt S) (hM:Rays.covariantTensor M)

def holder : Pill G where
    f := Complex.reCLM ∘ R.force M
    valid := (Maskable.color_force ..).applies _ Complex.reCLM.contDiff
    inv x U := congr_arg Complex.reCLM (R.force_gauge M hM x U)
    rank := r+1
    bound := by
       obtain ⟨S,hS⟩:= R.fitsAt_support; exact byStamp (S:=S) (by rw [show ((r+1:ℕ):ℤ)=(r:ℤ)+1 by norm_cast]; exact (R.force_affordable hS M).postcomp Complex.reCLM)

def sink : Pill G where
    f := Complex.reCLM ∘ R.compression M
    valid := (Maskable.color_compress ..).applies _ Complex.reCLM.contDiff
    inv x U := by obtain ⟨S,hS⟩:= R.fitsAt_support; exact congr_arg (fun z:ℂ=> z.re) (R.compression_gauge hS M hM x U)
    rank := r-1
    bound := by
       by_cases he : r=0
       · rw [show r-1=0 by omega]; exact rayZero ((Maskable.color_compress ..).applies _ Complex.reCLM.contDiff)
       obtain ⟨S,hS⟩:= R.fitsAt_support; exact byStamp (S:=S) (by rw [show ((r-1:ℕ):ℤ)=(r:ℤ)-1 by omega]; exact (R.compression_affordable hS M).postcomp Complex.reCLM)
-- first=valence minus one Mor.Crop third. multiply X^whatever. use Roll directly on towers.
abbrev shadeShift (r : ℕ) := (r-1)+2-(r+1)
lemma shade_sense : r+1+shadeShift r=(r-1)+2:=by unfold shadeShift; omega
def award: Era G ℝ:= (holder R M hM).letter - trim (PowerSeries.X^shadeShift r) (sink R M hM).letter
lemma coverAward: Auth (r+1) (award R M hM):= (holder R M hM|>.solid).sub (trim_auth _ ((sink R M hM|>.solid).tall (show r-1≤r+1 by omega)))
section leading
lemma real_ten {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F] (g:F→ℂ)(x:F)(k:ℕ)(p:ContDiffAt ℝ k g 0): Tensor.diagonal (Tensor.coeff (Complex.reCLM ∘ g) k 0) x=(Tensor.diagonal (Tensor.coeff g k 0) x).re:=by
    unfold Tensor.diagonal Tensor.coeff; rw [Complex.reCLM.iteratedFDeriv_comp_left p le_rfl]; simp only [_root_.smul_apply,Complex.smul_re]; rfl
lemma real_lead (g:ℝ→ℂ)(k:ℕ)(p:ContDiffAt ℝ k g 0): WardBin.leading k (Complex.reCLM ∘ g)=(WardBin.leading k g).re:=by
    unfold WardBin.leading iteratedDeriv; rw [Complex.reCLM.iteratedFDeriv_comp_left p le_rfl]; rw [Complex.smul_re]; rfl
end leading
lemma real_eval (z:Labels.Label G h)(p:Labels.realBar z=z)(A:Jet G): (Labels.read A z.val)= Complex.ofReal (Labels.read A z.val).re:=by
    have he := congr_arg (fun y:Label G h=>Labels.read A y.val) p; change Labels.read A (Labels.conjPol z.val)=_ at he; rw [conj_value] at he; have ht:= congr_arg Complex.im he; refine Complex.ext ?_ ?_; rfl; rw [Complex.ofReal_im]; change - _ = _ at ht; linarith
lemma primary_award {F:Frame G h}(v:Labels.Label G h)(p:realBar v=v)(u:v∈Grade (d,r+1))(q:v∈Maxwell.equationIdeal G h) (i:TagIx F (r+1))(hz:wT F i≤d): row F ((award R _ (tensor_eqv u)).2 0 (r+1)) i = if wT F i=d then ((F.coords v) i).re else 0:=by
    let H':= toTensor (r+1) v; let P:=holder R _ (tensor_eqv u); let Z:=sink R _ (tensor_eqv u); let X:= trim (PowerSeries.X^shadeShift r) Z.letter; let k:= wT F i; have he := seed_row H (coverAward R H' (tensor_eqv u)) (e:=0) i
    have hx : X.2 0 (r+1)=0:= (trim_auth _ Z.solid).coverN 0 (r+1) (by change r-1+0< _; omega)
    have hy : (award R H' (tensor_eqv u)).2 0 (r+1) = P.letter.2 0 P.rank:=by change P.letter.2 0 (r+1)- X.2 0 (r+1)= P.letter.2 0 (r+1); rw [hx,sub_zero]
    let T:Label G h:= ⟨seedTile (vitre h ((award R H' (tensor_eqv u)).2 0 (r+1))) k,fundedSeed H (coverAward R H' (tensor_eqv u)) (F.bound i.val)⟩
    have hφ : T=(if k=d then v else 0):=by
      apply Subtype.ext; apply Labels.eval_ext; intro A
      change Labels.read A (seedTile _ k)= _; erw [hy, P.principal_tile H A]
      let V:=R.force H' ∘ curve (d:=h) H; let W(x:Snap G h):= Complex.reCLM (V x); let Y:= fun t:ℝ=>engineered t (trunk h A); let A'(t:ℝ):= Tensor.diagonal (Tensor.coeff V (r+1) 0) (Y t)
      change Complex.ofReal (WardBin.leading k (fun t:ℝ=> Tensor.diagonal (Tensor.coeff W (r+1) 0) (Y t)))= _
      obtain ⟨S,hS⟩:= R.fitsAt_support
      have ht: ContDiff ℝ k A':= (Tensor.diag_smooth _ _).comp (eng_cont ..)
      have hc (t:ℝ): Tensor.diagonal (Tensor.coeff W (r+1) 0) (Y t)=Complex.reCLM (A' t):= real_ten _ _ _ ((R.force_affordable hS H').smooth_poly H h|>.of_le (WithTop.coe_le_coe.mpr le_top))
      rw [show (fun t:ℝ=> Tensor.diagonal (Tensor.coeff W (r+1) 0) (Y t))=Complex.reCLM ∘ A' from funext hc, real_lead _ _ ht.contDiffAt, show WardBin.leading k A'= _ from R.engineering_jet u q A hz]
      split_ifs with hp; · exact (real_eval _ p A).symm
      rw [Complex.zero_re,Complex.ofReal_zero]; exact (map_zero _).symm
    rw [he]; change ((F.coords T) i).re= if k=d then _ else _; rw [hφ]; split_ifs with h; rfl; rw [map_zero]; rfl
end Pill
end YM.WilsonCoeffUV.Mer.Xa
