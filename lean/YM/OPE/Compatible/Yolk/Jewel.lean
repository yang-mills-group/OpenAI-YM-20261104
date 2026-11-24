import YM.OPE.Compatible.Yolk.Vest
/-!
# R, rep and exact push, quantitative touch budget. Budget linear weight using probability represented kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
def Cinch (R:Rep G f)(S:StepData c f)(t e:ℝ) (V:Config G c):=∀ M: Leaf S R,
     ‖S.push R.beta M.cicada V‖≤e*(S.push R.beta R.eval V)*Real.exp (t * coverNumber R.p.B M.crest)*M.weight
def Besotted (R:Rep G f)(S:StepData c f)(t e:ℝ) (V:Config G c) (w:ℝ):=∀ X Y:Support f,X⊆ Y → Y.Nonempty → ∀ (f:Config G f→ℝ)(v:ℝ),Paced R Y S f v→
     ‖S.push R.beta (fun U=> smudge R X U*f U) V‖≤Real.exp (t * coverNumber R.p.B Y) * (Real.exp ((Y.card:ℝ)*w)-1)*e*S.push R.beta R.eval V*v
lemma Paced.env {Y:Support f}{h:Config G f→ℝ} (hb:Paced R Y S h w):Envelope h:=⟨hb.meas,w,hb.bound⟩
lemma beaming (K:Keeper R.p R.activities)(H:R.Lawful σ C Λ E w){V:Config G c}{t e:ℝ}(hh:Cinch R S t e V) (hu:S.IsKernel R.beta G)(hf:0 ≤ e)(he:0 ≤ S.push R.beta R.eval V)(hm:0≤t)(hp:t ≤ R.p.supportExponent):Besotted R S t e V w:=by
   intro X Y hX hy f v h
   obtain ⟨b,hb⟩ := (show ∃ b,Geared R b w from H.labels.boundK)
   let J:={b:Finset ℕ // Anchor R.activities X Y b}
   choose M k hK hS hI hW hZ using fun z:J=> plays_Y K (z.property.1.mono (show towY R.activities X z.val⊆ z.val from filter_subset ..)) h hb.1 H.labels
   have hF:= spurts hX H f h.env k hu (fun i=>⟨hK i,hS i,hI i,hZ i⟩) V hy
   let g:= S.push R.beta R.eval V; let k(z:J):=Real.exp (t*coverNumber R.p.B (enrolY R.activities Y z.val))*(∏ j∈z.val,b j)
   have hP:0≤v:= (norm_nonneg _).trans (h.bound 1)
   have hc(z:J): ‖S.push R.beta (M z).cicada V‖ ≤ v* (e*g)*k z:=by
       apply (hh _).trans_eq; rw [hW z]; have hl : (M z).crest=enrolY R.activities Y z.val:=by unfold Leaf.crest; rw [hK]; exact hS z
       rw [hl]; unfold k g; ring
   have ht : SumBudget k (Real.exp (t*coverNumber R.p.B Y) * (Real.exp ((Y.card:ℝ)*w)-1)):=gloaming hb hm hp
   have hx:= budget_scale (mul_nonneg hP (mul_nonneg hf he)) ht; have hu:=budget_mono hx (fun _=> norm_nonneg _) hc
   rw [← hF.tsum_eq]; apply (norm_tsum_le_tsum_norm hu.2.1).trans (hu.2.2.trans_eq ?_); ring
-- consumer gifts
lemma scalar_z (X:Coat T F) (_H:Cash W X.x μ L Q o C T R)(M:Leaf S R):
   jewelDebt M.tin_ Q L X.x= Real.exp ((R.p.supportExponent-Q.ε)*coverNumber R.p.B M.crest)*M.weight / Q.goal L X.x:=by
   unfold jewelDebt BudgetPoint.mass; rw [M.colorCue.1,← mul_right_comm,← Real.exp_add]; congr 3; ring
lemma granted (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (hk:X.width=o.K)(he: RG.flags (Pressure.temp X.x) X.V=∅)
 {a δ b:ℝ}(hy:Cash.Renewed m a δ b H) (hx:((X.B*2+1:ℕ):ℝ)^4*(Q.overture L μ X.x m*(1-1/2)⁻¹)≤ Q.exp)(hf:foam Q L)(hR:R.p.B ≤ 2* X.B)(hp:(swing Q L μ R.beta X.x C).Buy S.patch.L Q.halo X.B):
   Cinch R S (R.p.supportExponent-Q.ε) ((swing Q L μ R.beta X.x C).ceiling 0 0 0 0 / Q.goal L X.x) X.V:=by
    intro M; apply (M.tastes X H hk he hy hx hf hR hp).trans_eq; rw [scalar_z X H M]; ring
end YM.PhysicalNext.Repeat.Aroma
