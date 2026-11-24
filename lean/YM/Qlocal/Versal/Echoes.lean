import YM.Qlocal.Versal.Marsh
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Metric Lattice Laurent RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open Quipu Quipu.Lasso Quipu.Sonnet Marker
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge}{c f C F c' f': Side}{i j k n m r M D D':ℕ}{g t a d:ℝ}
  {V:Type}[DecidableEq V]{R:Marker.Census V}
variable (S:Tale R G)(X:S.Decision)(s:Senses R) (hc:C.val=c.val*D) (o: V→Site f) (O:V→Site F)
set_option quotPrecheck false
variable {P:Patch}(h:f.val=c.val*P.L.val) (H:F.val=C.val*P.L.val)
local notation "hF"=> Deck.fineP h H hc
local notation "q"=> Sonnet.root s
local notation "P0"=>o q
local notation "H'"=>decreed H
local notation "UK"=> Macrame.splitter (Deck.divides (Deck.fineP h H hc))
local notation "Σ!"=> Macrame.splitter (Deck.divides hc)
open Macrame Slide Deck
namespace Marines
variable (x:Site C)
variable (F0: Flank hc o O h H s x M)
section dual
variable (hc':C.val=c'.val*D') (h':f'.val=c'.val*P.L.val)
-- conflict notation
local notation "σ"=> Macrame.splitter (Deck.divides hc')
noncomputable abbrev land : V→Site f':= fun i=> (Macrame.splitter (Deck.divides (Deck.fineP h' H hc'))) (O i) -- order h' H notation conflict
local notation "λ₀"=> land (P:=P) O H hc' h'
include F0
lemma salt : Flank hc' (land O H hc' h') O h' H s x M:= by exact ⟨F0.ties,fun _ _=>rfl,F0.fits⟩
lemma photoshop (hd:2≤c.val)(hd':2≤c'.val): (decreed h').residue ∘ (λ₀) =_root_.id ((decreed H).residue ∘ O) ∧ ∀ i∈ essence s,(decreed h').residue (land O H hc' h' i)=(decreed h).residue (o i) := by
 have ht(i:V) : (decreed h').residue (land O H hc' h' i)=(decreed H).residue (O i):=(Lace.project (H:=H) (h:=h') hc' hd').room _; exact ⟨funext ht,fun i hi=>(ht i).trans (Marines.phase s hc o O h H x F0 hd i hi).1⟩
end dual
-- stamp transfer on cockpit. True geometry all positions before Aux. Supports carry. Specify Art wrapper for markup geometry & ζ.O.State.W
variable (B: BudgetPoint) (z:ℕ) (g:ℝ)
include F0
lemma adulthood (e:Senses R) (hx:essence e⊆ essence s)(hh:0<z)(ha:Tale.Live o e z)(hw:2*border P M<f.val) : Tale.Live O e z:= (turn_t e (Deck.fineP h H hc) O o (pen s hc o O h H x F0 e hx) (fun i hi=>F0.sailing i (hx hi)) hw).mpr ha
lemma salute (hd: border P M+z<f.val) (e:Senses R)(he:essence e⊆essence s): S.wake e (S.short X z) o g=S.wake e (S.short X z) O g ∘ (normal (Deck.divides hF) hF).links:= by ext1 U; exact precedes S X e (Deck.fineP h H hc) _ o (pen s hc o O h H x F0 e he) (fun i hi=> F0.sailing i (he hi)) (by omega) U
section
variable (hc':C.val=c'.val*D') (h':f'.val=c'.val*P.L.val)
local notation "λ₀"=> land (P:=P) O H hc' h'
open RGComparison01.Pledge
variable (xh:2*(2*M)≤c'.val)
noncomputable abbrev painting := Rotunda.bake (G:=G) (Σ! x) ((Macrame.splitter (Deck.divides hc')) x) xh
-- requires M>2 OR halo.B.Store. Eq for ALL U. cost on mask from AUX (could V' huge all links, equality still). calendar call Theta.App.B.Wt.Clock.
lemma nearness (p:BudgetPoint)(hX:S.Allows a d)(ha:0<a)(hg:0 < g) (hh: 2 ≤ c.val) (hh':2 ≤ c'.val) (hy:2*M<c.val)(hr0:2*M<c'.val)(hr: p.B≤M) (hZ:z≤p.B)(hC:2*(M+1)< C.val)(U:Config G c) :
   S.wake s (S.short X z) ((decreed h).parent ∘ o) g U = S.wake s (S.short X z) ((decreed h').parent ∘ (land O H hc' h')) g (painting hc x hc' xh U) := by -- `painting` may incl F0/s he (include?)
 let H0 : Flank hc' (λ₀) O h' H s x M:= Marines.salt s hc o O h H x F0 hc' h'; have he'(i:V)(he:i∈essence s):=((Marines.phase s hc' (λ₀) O h' H x H0 hh' i he).2)
 have he(i:V)(he:i∈essence s):=((Marines.phase s hc o O h H x F0 hh i he).2)
 let o'' := (decreed H).parent ∘ O
 let U': Config G c':= painting hc x hc' xh U
 let W:= S.wake s (S.short X z) o'' g; let V0:= (normal (Deck.divides hc) hc).links U; let V1:= (normal (Deck.divides hc') hc').links U'; have hu:= Marines.helmet s hc o O h H x F0
 have hz : x=o'' q:= F0.ties.symm
 let L:=Tale.court p.B x; have hQ : p.Regular L W:= by
     have hx:S.Allows (0+a+0) d:= by rw [zero_add,add_zero]; exact hX
     have hb:= Tale.shortBook p (Equiv.refl Axis) s S X o'' (t:=0) (d:=0) (by rw [zero_div]) le_rfl le_rfl ha (le_refl (0:ℝ)) hx hZ hg
     rw [← hz] at hb; exact hb.genuine
 refine (precedes S X s hc o'' ((decreed h).parent ∘ o) hu he (by omega) U).trans ((hQ.sites V0 V1 ?_).trans (precedes S X s hc' o'' ((decreed h').parent ∘ (λ₀)) hu he' (by omega) U').symm)
 apply agrees_mono (Slide.readNear x hC ?_)
 · intro i hi; apply (neighbors_mem ..).mpr (le_trans _ hr); simpa only [L,Tale.court,halo_spec,mem_singleton,exists_eq_left] using (show i∈ L from hi)
 unfold V0 V1; rw [Slide.rolls,Slide.rolls]; intro i hi hj; exact (Rotunda.aim (Σ! x) _ U xh i hi hj).symm -- signature
end
end Marines
end YM.Qlocal.Versal
