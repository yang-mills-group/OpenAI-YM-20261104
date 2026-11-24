import YM.OPE.Compatible.Nut.Wort
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
namespace Zest
section
-- readiness.Peak specialized.Admissibility
open Stroke Ibis Borealis Borealis.Galea Extra.Multi Labels Source Pressure Cameo
variable {K:Sponsor G}{T:Seasons K}{L:Host K T}{A:Labels.Frame G k}{S:SectionData A}{P: A.Coeff → Coefficient A L.f}{Q:A.Coeff → Coefficient A L.c}{H:Hol G} {U:Rep G L.c}
variable (x:A.Coeff)(p:Torch S H 0 L.P P m v)(F:Spells.Pad G)(a:ℂ→L[ℝ]ℝ) (q:Torch S H 0 U Q m s)
include x
noncomputable abbrev ViewerQ :Viewer L:= ⟨p.B,0,L.P.p,F,Torch.caged x p,a,Torch.γage p⟩
lemma ΩPledge : Viewer.Pledge (ViewerQ x p F a) (Torch.πcost x p) (m+6):= ⟨Torch.accepted x p⟩
noncomputable abbrev CoQ (L:Host K T){U:Rep G L.c}{Q:A.Coeff → Coefficient A L.c}(x:A.Coeff)(q:Torch S H 0 U Q m s)(F:Spells.Pad G)(a:ℂ→L[ℝ]ℝ):CoT L:= ⟨U.p,q.B,Torch.caged x q,a,0,F,Torch.γage q⟩
lemma Puoy : (CoQ L x q F a).Note (Torch.πcost x q) (m+6):= Torch.accepted x q
omit x in
private lemma brightX (U:Rep G L.c)(x:Config G L.c)(q: Coefficient A L.c)(hr:RG.flags U.p.threshold x=∅) : 0 < U.eval x ∧ q.density 0 S U x = (U.eval x:ℂ) * q.exponentialEntry 0 S U x:=by
   refine ⟨?_,?_⟩
   · unfold Rep.eval;rw [Activities.gas_one _ _ hr,mul_one];exact Real.exp_pos _
   have hx(b:Finset ℕ): q.marked U b x=0:=by
        unfold Coefficient.marked; split; swap; · rfl
        next h=>
             obtain he|⟨i,hi⟩:= b.eq_empty_or_nonempty; · subst b; exact Finset.sum_empty
             have hv : (U.activities.forced i).inventory⊆ b.biUnion (fun j=> (U.activities.forced j).inventory):= Finset.subset_biUnion_of_mem (fun j=> (U.activities.forced j).inventory) hi; rw [h.2,hr] at hv; exact False.elim ((U.activities.forced i).inventory_ne.ne_empty (Finset.subset_empty.mp hv))
   unfold Coefficient.density; simp_rw [hx]; simp
abbrev Trace₀ (L:Host K T)(f: Config G L.f→ℂ)(g:Config G L.c)(a:ℂ→L[ℝ]ℝ):=a (L.Z.push L.P.beta f g)/L.Z.push L.P.beta L.P.eval g
variable (y:A.Coeff)(g:Config G L.c) (M:ℝ)
lemma δBubble (hr: U.eval g=L.Z.push L.P.beta L.P.eval g)(hs: (Q x).density 0 S U g = M • (L.Z.push L.P.beta ((P y).density 0 S L.P) g))(h: RG.flags U.p.threshold g=∅): ‖a (Torch.caged x q g)-M*Trace₀ L ((P y).density 0 S L.P) g a‖≤ ‖a‖*(clove A q.c x *Ξoff U.p):=by
         obtain ⟨ht,hU⟩:= brightX (L:=L) U g (Q x) h (S:=S)
         let z:= (Q x).exponentialEntry 0 S U g; have he : Healthy U.p.threshold (Spindle.patch q.B (0:Site L.c)) g:= by unfold Healthy;rw [h];simp
         let t:= U.eval g; have hk(t:ℝ)(z:ℂ): (t:ℂ)*z=t • z:= by rfl
         let u:=a (L.Z.push L.P.beta ((P y).density 0 S L.P) g); have hh:t*a z=M*u :=by
                rw [hk] at hU; exact (show t*a z=a _ from (a.map_smul t z).symm).trans ((congr_arg a (hU.symm.trans hs)).trans (a.map_smul ..))
         have hp: M*Trace₀ L ((P y).density 0 S L.P) g a = a z:=by unfold Trace₀; rw [←hr]; change M*(u/t)=_; rw [←mul_div_assoc,←hh]; exact mul_div_cancel_left₀ (a z) (show t≠0 from ht.ne')
         rw [hp, ← _root_.map_sub]; apply (a.le_opNorm _).trans; rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left ((q.taxes x).2 g he) (norm_nonneg _)
end
end Zest
end YM.OPE.Lass
