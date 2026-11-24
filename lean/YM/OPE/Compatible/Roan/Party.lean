import YM.OPE.Compatible.Roan.Stone
/-! # moments Pu and κ sums at all.Per tick.Masks -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m n n':ℕ}{t C s u z ℓ v a c e r e' s' R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T) (Y:Studio L)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "μ"=> Y.μφ
open Lav
variable {N:ChartRatio G}(hN:LocalRatio N)(H:StackP N r R t)
variable (h:L.Rich s c e v u C)(he:0<e)(ht:0<s)(hc:0≤c)(hp:0≤v)
abbrev alongB (f:L.DirA→ℝ):= f ∘ Vlamp L Y
variable {p:Sender L}
abbrev crestQ (L:Host K T)(p: Sender L)(Y:Studio L):= fun x=> p (Vtone L Y x)
include h he ht hc
lemma BonP (i:RodZ L k) : Pu μ (Gale L Y i):= (Bsafe L Y i h ht hc he (show Scale Y (‖Y.w‖+‖Y.ext‖) from ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (norm_nonneg _)⟩)).pu
lemma Quala (X:Seats L.ForestQ)(hv:Funded L X p a k): AgeT μ (crestQ L p Y):= ⟨fun i=>(Fans (t:=‖Y.w‖+‖Y.ext‖) (Y:=Y) h ht hc he ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (norm_nonneg _)⟩ X le_rfl p hv i).pu⟩
variable {f w:L.DirA→ℝ}{p': PinS L n}{q': PinS L n'}
omit h he ht hc in
lemma cordial (h:Yields L f n p' s t): alongB L Y f=∑ j:Site L.f,∑ i,p' j i • Gale L Y i:=by
       funext x; rw [Finset.sum_apply,alongB,Function.comp_apply,h.pays]; refine Finset.sum_congr rfl (fun i _=>?_); rw [Finset.sum_apply]; refine Finset.sum_congr rfl (fun j _=>?_); rw [Pi.smul_apply,smul_eq_mul]; congr 1; unfold Gale; rw [Finset.prod_apply]; rfl
lemma PuCon (hv:Yields L f n p' r R): Pu μ (alongB L Y f):=by rw [cordial _ Y hv]; exact PuSum _ _ (fun j _=> PuSum _ _ (fun i _=> scaleP (BonP L Y h he ht hc i) _))
lemma PuTour {s' t':ℝ}(hv:Tires L f n s' t'): Pu μ (alongB L Y f):=by obtain ⟨f,hp⟩:=hv; exact PuCon _ _ h he ht hc hp
variable {g f':Y.St→ℝ}
lemma coinX (hv:Yields L f n p' r R)(hx:Pu μ g): κ2 μ g (alongB L Y f)=∑ j:Site L.f,∑ i,p' j i*κ2 μ g (Gale L Y i):=by
       let b:= fun i=> Gale L Y (k:=n) i; let a(j:Site L.f):= ∑ i,p' j i • b i; rw [cordial L Y hv]; have hh : κ2 μ g (∑ i,a i)= ∑ i,κ2 μ g (a i):=by
               have he:=PuPier hx a Finset.univ (fun i _=>PuSum _ _ (fun i _=>scaleP (BonP L Y h he ht hc i) _)) (fun i=>1); simpa using! he
       rw[hh]; exact Finset.sum_congr rfl fun j _=> PuPier hx _ _ (fun i _=>BonP L Y h he ht hc i) _
lemma bornX (hv:Yields L f n p' r R) (hx:Pu μ g)(hf:Pu μ f') :κ3 μ g f' (alongB L Y f)=∑ j:Site L.f, ∑ i,p' j i *κ3 μ g f' (Gale L Y i):=by
       let b:= fun i=> Gale L Y (k:=n) i; let a(j:Site L.f):=∑ i,p' j i • b i; rw [cordial L Y hv]; have hh:κ3 μ g f' (∑ i,a i)= ∑ i, κ3 μ g f' (a i):=by
                have he:=PuPier3 hx hf a Finset.univ (fun i _=>PuSum _ _ (fun i _=>scaleP (BonP L Y h he ht hc i) _)) (fun i=>1); simpa using! he
       rw [hh]; exact Finset.sum_congr rfl fun j _=> PuPier3 hx hf _ _ (fun i _=>BonP L Y h he ht hc i) _
lemma EarthX (hv:Yields L f n p' r R)(hh:Yields L w n' q' e' s')(hx:Pu μ g): κ3 μ g (alongB L Y w) (alongB L Y f) =∑ j:Site L.f,∑ i,∑ k:Site L.f,∑ l,p' j i*q' k l *κ3 μ g (Gale L Y i) (Gale L Y l):=by
       rw [bornX L Y h he ht hc hv hx (PuCon _ _ h he ht hc hh)]; refine Finset.sum_congr rfl (fun j _=>Finset.sum_congr rfl (fun i _=>?_)); rw [(Order3 μ _ _ _).1,bornX L Y h he ht hc hh hx (BonP _ _ h he ht hc i),mul_sum]; exact Finset.sum_congr rfl (fun l _=>by rw [mul_sum];exact Finset.sum_congr rfl (fun i _=> (mul_assoc ..).symm))
end
end YM.OPE.Borealis.Galea
