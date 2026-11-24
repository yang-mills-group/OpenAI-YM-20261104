import YM.LocalLTE.Ballot.Yarn
import YM.LocalLTE.Vinca.Ports
/-! Credentials.Output K forced retained in FULL Transfer.Books with its ports.YouReads proof. Relative projection budget via exact layout.De.Minimal.Analytic class for next Key.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vinca
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (Y : Hol G){n: Side}
local notation "WorkSite" => n
variable (L:ℕ→Support n) (W:Raw F n)(E:ℕ→ Config G n→ℂ)(o:Site n)(R:Rep G n)
    {σ v κ μ Λ δ c C η b w e θ ζ t s :ℝ}
-- projection from local prognosticated current. B fixed. Not prediction of future. Canonical exact residual on THIS Y.
noncomputable def emit (t:ℝ)(x:F.Coeff)(V:ℕ→ Config G n →ℂ) : Coefficient F n:= { x:= x+∑' i, weighted Y F o (L i) t (V i), support:= fun i=> joint B o (L i),regular:= fun i=>residual Y B o (L i) t (V i), forced:=0 }
def decrement (P Q: Coefficient F n) : Coefficient F n:={P with x:=P.x-Q.x,regular:=P.regular -Q.regular,forced:=P.forced-Q.forced}
-- Prop witness doesn't shrink costs on existential variant. p/L exact.
structure Patched (P:BudgetPoint) (o:Site n)(L:ℕ→Support n)(g:ℕ→ Config G n→ℂ)(z:ℝ):Prop where
   permit : ∃ q:ℕ→ℝ, SumBudget (fun i=> reservedMass P (L i) (q i)) z ∧∀ i,P.Regular (L i) (g i)∧ P.supBounds o (L i) (g i) (q i)
section generic
variable {g f:ℕ→ Config G n→ℂ}{p:BudgetPoint}
open Next.Foundations
lemma stretchP (hg:Patched p o L g t)(hf:Patched p o L f s):Patched p o L (g-f) (t+s):=by
   obtain ⟨q,hQ,hq⟩:= hg.permit; obtain ⟨v,hV,hv⟩:= hf.permit
   refine ⟨(fun i=> q i+v i),?_ ,fun i=> ⟨regular_sub ((hq i).1) ((hv i).1), bound_sub ((hq i).1) ((hv i).1) ((hq i).2) ((hv i).2)⟩⟩
   simpa only [reservedMass,mul_add] using! Local.sumBudget_add hQ hV
lemma painted (hr: Local.Readable Y B p n e) (hI:∀ i,o∈L i) (hg:Patched p o L f t) : SumBudget (fun i=> F.coeffSize (weighted Y F o (L i) p.threshold (f i))) (factor Y B p.supportExponent e*t) ∧ (∃ b:ℕ→ℝ, SumBudget (fun i=> p.mass (joint B o (L i)) (b i)) (factor Y B p.supportExponent e*t)∧∀ i, p.supBounds o (joint B o (L i)) (residual Y B o (L i) p.threshold (f i)) (b i)):=by
   obtain ⟨b,hB,hb⟩:=hg.permit
   let Lx:= factor Y B p.supportExponent e; have hr':0≤ Lx:= zero_le_one.trans (Dilation.factorLarge hr)
   let a:= atomPrice Y F e; have ha:1≤ a:= atomPrice_ge_one Y F hr.nonneg; let g i:= a*b i; have hk i:0≤g i:=mul_nonneg (zero_le_one.trans ha) (hb i|>.2.1)
   have ht:= Local.sumBudget_mul_left hB hr'; let v i:=p.mass (joint B o (L i)) (g i)
   have hh i: v i≥ g i:= p.loMass _ _ (hk i)
   have hc: SumBudget v (Lx*t):= Local.sumBudget_mono ht (fun i=> (hk i).trans (hh i)) (fun i=> (show v i≤ reservedMass p (joint B o (L i)) (g i) from mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (hk i)).trans (price_join B Y o (hI _) hr.sound hr.nonneg (hb i|>.2.1))) le_rfl
   have hκ: readPrice Y F≤ a:=by unfold a atomPrice; have hF:= readPrice_pos Y F; nlinarith [hr.nonneg]
   exact ⟨Local.sumBudget_mono hc (fun i=> Work.G08.size_nonneg ..) (fun i=> (weighted_bound Y F o (hb i|>.1) hr.order hr.power (hb i|>.2)).trans ((mul_le_mul_of_nonneg_right hκ (hb i|>.2.1)).trans (hh i))) le_rfl,⟨g,hc,fun i=> (charge_atom o hr (hb i|>.1) (hb i|>.2)).1⟩⟩
-- prognosed outputs policy.Stem.Q.Matches sub.gs. Closure for actual contour.
lemma subK (L:Support n)(g f:Config G n→ℂ)(hg:p.Regular L g)(hh:p.Regular L f)(hz:d≤p.order): weighted Y F o L t (g-f) = weighted Y F o L t g - weighted Y F o L t f:=by
   apply eq_sub_of_add_eq; have hp:= Next.Foundations.regular_sub hg hh; unfold weighted; rw [← map_add,←map_add,← project_add Y o hp hh hz]; rw [sub_add_cancel]
lemma separate (hr:Readable Y B p n e)(hI:∀ i,o∈L i) (hg:Patched p o L g t)(hp:Patched p o L f s)(y:F.Coeff): decrement (Vinca.emit B Y L o p.threshold y g) (Vinca.emit B Y L o p.threshold y f) = Vinca.emit B Y L o p.threshold 0 (g-f):=by
   let ζ:= p.threshold
   have hh i := (hg.permit.choose_spec.2 i).1
   have he i:= (hp.permit.choose_spec.2 i).1
   have hu i : weighted Y F o (L i) ζ ((g-f) i) = _:= subK Y o (L i) _ _ (t:=ζ) (hh i) (he i) hr.order -- order edit
   unfold decrement Vinca.emit; congr 1
   · let A i:= weighted Y F o (L i) ζ (g i); let Z i:= weighted Y F o (L i) ζ (f i)
     have hA: Summable A:= (Size.series F ((painted B Y L o hr hI hg).1.2.1)).of_norm; have hZ: Summable Z:= (Size.series F ((painted B Y L o hr hI hp).1.2.1)).of_norm
     rw [show p.threshold=ζ from rfl]; simp_rw [hu]; rw [hA.tsum_sub hZ]; abel
   · funext i; unfold Local.residual; dsimp only [Pi.sub_apply]; rw [show p.threshold=ζ from rfl, subK _ _ _ _ _ (hh _) (he _) hr.order, map_sub]; abel
   simp only [sub_zero]
end generic
local notation "K"=> factor Y B R.p.supportExponent t
local notation "Ip"=> Vinca.emit B Y L o R.p.threshold
open Next.Foundations
lemma snapshot (S:Berths R.p R.activities (fun i=>joint B o (L i))) (hr: Local.Readable Y B R.p n t)(hX: W.Format o L R) (h:Patched R.p o L W.bulk v)(hk:R.Lawful σ C Λ δ w) (hv : Patched R.p o L (W.bulk-E) e)(hT:ForceCost R.p R.activities (mint S W Y).forced (κ*θ)) (hkappa:0<κ)(hθ:0≤θ): let Z:=mint S W Y
     let Vc:=Vinca.emit B Y L o R.p.threshold W.seed E; let p:= decrement Z Vc; Patched R.p o L E (v+e) ∧ Vc.support=Z.support∧ Vc.Format o Y R ∧ Tab Vc o R κ (K*(v+e)) 0 ∧ p.Format o Y R ∧ Tab p o R κ (K*e) θ ∧ F.coeffSize p.x ≤ K*e:=by
   intro Z Vc p
   let Mv:= Ip W.seed E; have hs: Patched R.p o L E (v+e):= sub_sub_cancel W.bulk E ▸ (stretchP L o h hv)
   have hp: Vc.support = p.support:=rfl
   have hy : p.x= (Ip 0 (W.bulk-E)).x∧ p.regular=(Ip 0 (W.bulk-E)).regular:=by
       have hQ:= separate B Y L o hr hX.origin h hs W.seed; have hx:= congr_arg Coefficient.x hQ; have ht:=congr_arg Coefficient.regular hQ; exact ⟨hx,ht⟩
   have ht : Z.Format o Y R:= Guard.usage S hX hk hr
   have hz: ForceFormat R.p R.activities o (0:ℕ→ Config G n→ℂ):= ⟨fun _ _ h=>False.elim (h rfl),fun _ h=>False.elim (h rfl),fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
   have hZ : ForceCost R.p R.activities (0:ℕ→ Config G n→ℂ) (κ*0):=by simp only [mul_zero]; exact ⟨(fun _=>0),by simp [SumBudget,BudgetPoint.mass]⟩
   have he:= painted B Y L o hr hX.origin hs; have hE:= painted B Y L o hr hX.origin hv; have hf: p.forced=Z.forced:=by change _-0=_; exact sub_zero _
   have hρ : Z.forced=p.forced:=hf.symm
   refine ⟨hs,rfl, ?_,⟨hkappa,sumBudget_credit he.1, le_rfl, he.2,hZ⟩,?_, ⟨hkappa,sumBudget_credit hE.1,hθ,?_,hf.symm ▸ hT⟩,?_⟩
   · have hp i:=convert_atom o hr (show R.p.Regular (L i) (E i) from hs.permit.choose_spec.2 i|>.1)
     exact ⟨fun i=> (hp i).1,ht.origin,fun i=> ((Next.Foundations.reads_null_iff ..).mp (hp i).2.2.1).1,fun i=>((Next.Foundations.reads_null_iff ..).mp (hp i).2.2.1).2,hz.forcing,hz.carried,hz.invariant,hz.supported,hz.borel⟩
   · have he i:= convert_atom o hr ((hv.permit.choose_spec.2 i).1)
     refine ⟨hy.2.symm ▸ (fun i=> ?_),ht.origin,hy.2.symm ▸ (fun i=>?_),hy.2.symm ▸ (fun i=>?_), hf.symm ▸ ht.forcing, hf.symm ▸ ht.carried, hf.symm ▸ ht.invariant,hf.symm ▸ ht.supported,hf.symm ▸ ht.borel⟩
     · exact (he i).1
     · exact ((Next.Foundations.reads_null_iff ..).mp (he i).2.2.1).1
     exact ((Next.Foundations.reads_null_iff ..).mp (he i).2.2.1).2
   · rw [hy.2]; exact hE.2
   rw [hy.1]; change F.coeffSize (0+_)≤_; rw [zero_add]; exact (Size.bound F hE.1.2.1).trans hE.1.2.2
end YM.LocalLTE.Vinca
