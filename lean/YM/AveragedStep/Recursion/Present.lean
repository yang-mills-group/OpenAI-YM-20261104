import YM.AveragedStep.Recursion.Rook
/- Supplies before extraction, compress finite-index simultaneous
cost after chart but before volume data. Cash-in in Recovery. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform

private lemma hunt {I: Type} [Fintype I] (P:I→ℝ→ℝ→ℕ→Prop) (H:∀ (τ:ℝ), 1 ≤ τ → ∀ i (r t:ℝ), 0 ≤ r → r ≤ t → ∀ (x y:ℕ), x ≤ y → P i τ r x → P i τ t y)
    (h:∀ i,∃ C:ℝ,∃ n:ℕ,0≤C∧∀ᶠ τ:ℝ in atTop,P i τ C n):∃ C:ℝ,∃ n:ℕ,0≤C∧∀ᶠ τ:ℝ in atTop,∀ i,P i τ C n:=by
 choose C n hc h' using h
 refine ⟨∑ i,C i,∑ i,n i,Finset.sum_nonneg fun i _=>hc i,?_⟩
 filter_upwards [eventually_all.mpr h',eventually_ge_atTop (1:ℝ)] with τ h hk
 exact fun i=>H τ hk i (C i) _ (hc _) (Finset.single_le_sum (fun i _=>hc i) (Finset.mem_univ _)) (n i) _ (Finset.single_le_sum (fun i _=>Nat.zero_le _) (Finset.mem_univ _)) (h i)

section presents
variable {G:Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}(Q:Cuff P K A)
    (hA:LocalRatio A)(hS:P.Branches K G){L D δ:ℝ}(hQ:Cadence Q L D δ)
-- make U and F universal here, so occurrence/hyp at lower order can specialize
-- even if goal eventually consumed on a unique family.
def Ticket (a:ℝ)(τ:ℝ)(d n k:ℕ)(B:ℝ)(q:ℕ):Prop:= ∀{c f:Side}(S:StepData c f)(F:Forest S.ratio)(hP:S.patch=P)(hK:S.kernel=K),Window G S τ P K → Bid.Larger (G:=G) S → ∀ x:Site c,∀ (u:Config G c→ℝ), Envelope u→(∀ p, |u p|≤1)→ ∀ U:Azure A F,
    let q':Cuff S.patch S.kernel A:=hP.symm ▸ hK.symm ▸ Q
    Fund (S:=S) (τ:=τ) (a:=a) (S.ratio.embed x) (lessons F q' x τ u U d) d n k B q
def Covered (d n k:ℕ):Prop:=∀ a:ℝ,0<a→∃ B:ℝ,∃ q:ℕ,0≤B∧∀ᶠ τ in atTop,Ticket Q a τ d n k B q
lemma authorized {a τ B C:ℝ}{d n k q r:ℕ}(H:Ticket Q a τ d n k B q)(ht:1≤τ)(hb:0≤B)(h: B≤C)(hr:q≤r): Ticket Q a τ d n k C r:= fun {_ _} S F hP hK hz he x u hu hq U=> (H S F hP hK hz he x u hu hq U).payable ht hb h hr
lemma advance {I:Type}[Fintype I]{d k n:I→ℕ}{a:ℝ}(ha:0<a)(Hp:∀ i,Covered Q (d i) (n i) (k i)):
    ∃ B:ℝ,∃ q:ℕ,0≤B∧∀ᶠ τ in atTop,∀ i,Ticket Q a τ (d i) (n i) (k i) B q:=hunt (fun i τ B q=> Ticket Q a τ (d i) (n i) (k i) B q) (fun _ hT _ _ _ hA h _ _ hK U=> authorized Q U hT hA h hK) (fun i=>Hp i a ha)

def Invoice(a τ:ℝ)(d k:ℕ)(l:G.ColorIndex)(B:ℝ)(q:ℕ):Prop:= ∀{c f:Side}(S:StepData c f)(F:Forest S.ratio)(hP:S.patch=P)(hK:S.kernel=K),Window G S τ P K → ∀ x:Site c,∀ (u:Config G c→ℝ),Envelope u →(∀ p,|u p|≤1)→
   let q':Cuff S.patch S.kernel A:=hP.symm ▸ hK.symm ▸ Q
   ∀ (w:Lips G c f),w.length=k→ ∀ i:F.Free,|rust F q' x τ u (i,l) w d| ≤ B*stale τ d q*lens S a (S.ratio.embed x) (fieldKey F i l::w)
lemma Invoice.lift {τ a:ℝ}{d k l B q B' q'}(h:Invoice Q a τ d k l B q)(ht:1≤τ)(hB:0≤B)(hB':B≤B')(hQ':q≤q'):Invoice Q a τ d k l B' q':=by
 intro c f S F hP hK he x u hv hh C w hw i
 apply (h S F hP hK he x u hv hh w hw i).trans
 exact mul_le_mul_of_nonneg_right (mul_le_mul hB' (stale_mono ht d hQ') (stale_pos ht ..) (hB.trans hB')) (lens_pos ..).le

include hQ hA hS in
lemma invoices (a:ℝ)(ha:0<a)(d k:ℕ):∃ B:ℝ,∃ q:ℕ,0≤B∧∀ᶠ τ in atTop,∀ j l,j≤k→Invoice Q a τ d j l B q:=by
 let I:= Fin (k+1) × G.ColorIndex
 have h (i:I):∃ (C:ℝ)(q:ℕ),0≤C∧∀ᶠ τ in atTop,Invoice Q a τ d i.1.val i.2 C q:=by

   let v:=2*i.1.val+2*d+6
   obtain ⟨B,hB,H⟩:= by_plant hQ hA hS i.2 i.1.val d a ha
   refine ⟨B,v+(d+1),hB,?_⟩
   filter_upwards [H] with τ h c f S F hP hK hz x u hu hT C w hw j
   unfold stale lens rust
   rw [steps_cons]
   exact (h S F hP hK hz w hw x j u hu hT).trans_eq (by dsimp only [tolls,v,fieldKey]; ring)
 obtain ⟨B,q,hB,H⟩:=hunt (I:=Fin (k+1) × G.ColorIndex) (fun i τ B r=>Invoice Q a τ d i.1.val i.2 B r) (fun τ ht _ _ _ h1 h2 _ _ hv=>fun H=>H.lift Q ht h1 h2 hv) h
 refine ⟨B,q,hB,?_⟩; filter_upwards [H] with τ h j l he; exact h (⟨j,by omega⟩,l)
end presents
end YM.AveragedStep.SD
