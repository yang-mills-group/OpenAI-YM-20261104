import YM.OPE.Compatible.Roan.Party
/-! # Reports from LP canon. tensor trivial blossoms downstream. -/
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
include h he ht hc hp H hN
lemma constellation : Pu μ (alongB L Y (Rate3 L)) ∧ Pu μ (alongB L Y (Rate4 L N)):=by
       obtain ⟨he',hv⟩:= leafE L h he hc; have hh:= taper L hN H h he hp; refine ⟨PuTour L Y h he ht hc he',?_⟩; rw [tel4 L hN]; exact addedP (PuTour L Y h he ht hc hv) (PuTour L Y h he ht hc hh)
variable (p:Sender L)(X:Seats L.ForestQ)(hX:Funded L X p a k)
include hX
noncomputable abbrev Spex (p:Sender L)(i:Phase)(x:Y.St):ℝ:=((crestQ L p Y) x).seq i.val
lemma BitsG :
         let q(i):=Spex L Y p i
         let f:= alongB L Y (Rate3 L); let g:= alongB L Y (χ2 L N); let g':= alongB L Y (χ4 L)
         MuseY L p N Y=⟨a_ μ (q 0),a_ μ (q 1)+κ2 μ (q 0) f, a_ μ (q 2)+(κ2 μ (q 0) g'+κ2 μ (q 0) g)+κ2 μ (q 1) f+(2:ℝ)⁻¹ *κ3 μ (q 0) f f⟩:=by
                intro q f g g'; have he':=Quala L Y h he ht hc X hX; have hx:= constellation L Y hN H h he ht hc hp; let V:= alongB L Y (Rate4 L N); have hs:MuseY L p N Y= _:= Stats _ V (q 0) (q 1) (q 2) hx.1 hx.2 (he'.Γ 0) (he'.Γ 1) (he'.Γ 2); have hv:V=g'+g:=by unfold V; rw[tel4 L hN];rfl
                have hg:=PuTour L Y h he ht hc (taper L hN H h he hp); have hG:=PuTour L Y h he ht hc ((leafE L h he hc).2); have ht: κ2 μ (q 0) V= κ2 μ (q 0) g'+κ2 μ (q 0) g:=by rw [hv]; unfold κ2;rw [mul_add,Etick (w:=q 0*g') (timesP (he'.Γ 0) hG) (timesP (he'.Γ 0) hg),Etick (w:=g') hG hg]; ring
                rw[hs]; -- maybe ht occurs
                change (⟨a_ μ (q 0), a_ μ (q 1)+κ2 μ (q 0) f, a_ μ (q 2)+κ2 μ (q 0) V+κ2 μ (q 1) f+(2:ℝ)⁻¹* κ3 μ (q 0) f f⟩:Token)=_; rw[ht]
lemma ZVote (hs:Stowed Y.X Y.ext): Y.inkY N (crestQ L p Y)=MuseY L p N Y:=by
             let f:= alongB L Y (Rate3 L); let A:= crestQ L p Y; let g:= Y.glow N; let V(x):= CoatB L N (Y.V (Y.boat x)); let a:=jet (taxY Fθ N) 2 Y.ext; have hu : AgeT μ A:=Quala L Y h he ht hc X hX; obtain ⟨hx,hg⟩:= constellation L Y hN H h he ht hc hp; have hw(x:Y.St): V x=g x+⟨0,0,a⟩:= SweepJ hN L Y hs x h.home; have ht':AgeT μ g:=by
                  constructor; intro i; fin_cases i; · exact flipP _
                  · change Pu Y.μφ (fun x=>(g x).l); rw [show (fun x:Y.St=> (g x).l)= f from funext fun i=>by have hv:(V i).l=(g i).l+0:= congr_arg (·.l) (hw i); rw [add_zero] at hv;exact hv.symm]; exact hx
                  let v:= alongB L Y (Rate4 L N); have he(x): (g x).h=(v x+(2:ℝ)⁻¹ * (f x*f x))+(-a):=by have he:(V x).h=(g x).h+a:= congr_arg (·.h) (hw x); change v x+ _* (f x)^2=_ at he; rw [sq] at he; rw[he];ring
                  change Pu Y.μφ (fun x=>(g x).h); rw [show (fun x:Y.St=>(g x).h)=_ from funext he]; exact addedP (addedP hg (scaleP (timesP hx hx) ((2:ℝ)⁻¹))) (flipP _)
             rw [show Y.inkY N (crestQ L p Y)=Speak μ g A from ?_]; exact (show Speak μ g A= Speak μ V A from (by rw [AgeT.canon _ _ _ ht' hu (fun _=>rfl) a]; congr; exact (funext hw).symm))
             unfold Speak; rw [mul_comm]
end
end YM.OPE.Borealis.Galea
