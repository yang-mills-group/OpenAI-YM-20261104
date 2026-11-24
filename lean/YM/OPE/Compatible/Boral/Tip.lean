import YM.OPE.Compatible.Boral.Berries
/-! # Mutation retaining law. µ views and increments. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {N:ChartRatio G}(hN:LocalRatio N)
variable (L:Host K T) (p:Sender L)
local notation "Fθ"=> L.ForestQ
local notation "Yκ"=>AxisChart G Fθ
variable (Y:Studio L)
noncomputable abbrev ViewS (Y:Studio L): Yκ→L[ℝ] Y.St:= ChartUp L.Z Fθ Y.X L.F.L.Q
noncomputable abbrev Wκμ (Y:Studio L)(x:Yκ):= Y.V (Y.boat (ViewS L Y x))
lemma shutt (q:Y.St→ℝ): a_ (majr L) (q ∘ ViewS L Y)= a_ Y.μφ q:=by unfold a_; rw [has_p,has_p]; exact echoW _ _ _ (inflect Y.X L.F.L.Q) _ _ _
lemma BxP (Z Q:Y.St→Token): Speak (majr L) (Z ∘ ViewS L Y) (Q ∘ ViewS L Y)= Speak Y.μφ Z Q:=by
       have hx(Z:Y.St→Token): ηAvg (majr L) (Z ∘ ViewS L Y)= ηAvg Y.μφ Z:=by apply JetS.eta; exact shutt L Y (fun i=>(Z i).s); exact shutt L Y (fun i=>(Z i).l); exact shutt L Y (fun i=>(Z i).h)
       unfold Speak; rw [show (Q ∘ ViewS L Y)*(Z ∘ ViewS L Y)=(Q*Z) ∘ ViewS L Y from rfl,hx,hx]
lemma Yστε (N:ChartRatio G): MuseY L p N Y=Speak (majr L) (fun i=>CoatB L N (Wκμ L Y i)) (fun i=>p (Wκμ L Y i).2):=by unfold MuseY; exact (BxP L Y _ _).symm
noncomputable def worldA (x: Bid.Dir G L.c):Studio L:={ X:=univ, ext:=0, w:=x, Y:=univ }
lemma WalkF (x: Bid.Dir G L.c): Wκμ L (worldA L x)= stareD L x:=by
        let Y:= worldA L x; funext i; have hp(x:Yκ): stake Y.X (ViewS L Y x)=x:=by
             let f:= rip L.Z L.H G Y.X x; let T:= stake Y.X (G:=G); have hx:T f=x:= funext fun j=> stake_on Y.X (⟨j,Finset.mem_univ _⟩:↥Y.X) f; change T (ViewS L Y x)=x; nth_rw 1 [←hx]; rw [show ViewS L Y (T f)= _ from (show _=f from dryW T _ _ (inflect Y.X L.F.L.Q) f),hx]
        refine Prod.ext rfl ?_; let B:= L.F.L.M; change 0+stake Y.X (ViewS L Y i+ ViewS L Y (B x-0))=B x+i; rw [sub_zero, map_add,hp,hp,zero_add,add_comm]
include hN in
lemma tradeV (h:L.Rich s c e v u C)(he:L.b=0)(hs:G.Simple)(x:Bid.Dir G L.c): GPY L p N x=MuseY L p N (worldA L x):=by rw [Yστε,WalkF]; exact βRead hN L p h he hs _
include hN
variable (h:Stowed Y.X Y.ext)
include h
lemma tax_add (x:Y.St): jet (taxY Fθ N) 2 (Y.V x).2= jet (taxY Fθ N) 2 Y.ext+ jet (feeX N (F:=↥Y.X)) 2 x:=by
       let J:= Y.X; let p:= Y.ext; let f(z:G.Color):= jet (rake N) 2 z; let b(i:Yκ):=∑ j: (forest L.Z.ratio L.H).Free, f (i j); have hx:x=x:=rfl
       change jet (feeX N) _ _=jet (feeX N) 2 p+_; rw [levy hN,levy hN,levy hN]; change b (p+stake J x)= b p+ ∑ i:(J:Type),f (x i); have he(i:(forest L.Z.ratio L.H).Free): f ((p+stake J x) i)=f (p i)+ f (stake J x i):=by
             have hQ:f 0=0:=by unfold f jet; rw [(iteratedFDeriv ℝ 2 (rake N) 0).map_coord_zero (0:Fin 2) (by rfl),mul_zero]
             rw [Pi.add_apply]; by_cases ht:i∈J
             · rw [show p i=0 from h i ht,hQ,zero_add,zero_add]
             rw [stake_off J _ _ ht,hQ,add_zero,add_zero]
       unfold b; simp_rw[he]; rw [sum_add_distrib]; apply congr_arg; have ht:∑ i∈J,f (stake J x i)= ∑ i:(J:Type), f (x i):=by rw [← Finset.sum_attach J]; refine Finset.sum_congr rfl fun i _=> congr_arg f (stake_on J i x)
       rw [← ht]; refine Eq.symm (sum_subset (subset_univ _) (fun i hi hj=>?_)); rw [stake_off J _ _ hj]; unfold f jet; rw [(iteratedFDeriv ℝ 2 (rake N) 0).map_coord_zero (0:Fin 2) (by rfl),mul_zero]
-- cancellation density phase
lemma SweepJ (x:Y.St)(hv:fitsW L.A L.P): CoatB L N (Y.V (Y.boat x))= Y.glow N x+(⟨0,0,jet (taxY Fθ N) 2 Y.ext⟩:Token):=by
        have hp:= hv.path; have hz:Y.Hx x=Rate3 L (Y.V (Y.boat x)):=by unfold Studio.Hx haze; rw [hv.clip,hv.path]
        have hJ:Y.Ux N x+jet (taxY Fθ N) 2 Y.ext=Rate4 L N (Y.V (Y.boat x)):=by
              unfold Studio.Ux litter Rate4; rw [tax_add hN L Y h,hp,hv.clip]; change jet _ 2 _- jet L.PA _ (Y.V _)-jet L.PL 2 (Y.V _)+jet (taxY Fθ N) _ _=_; ring
        apply JetS.eta; · change 1=1+(0:ℝ); ring
        · change Rate3 L _= Y.Hx x+0; rw [hz,add_zero]
        change Rate4 L _ _+(2:ℝ)⁻¹* _ = (Y.Ux N x+(Y.Hx x)^2/2)+_; rw [←hJ,hz];ring
end
end YM.OPE.Borealis
