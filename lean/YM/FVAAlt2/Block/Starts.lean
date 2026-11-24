import YM.Integration.RunFormalCoefficients
import YM.FVAAlt2.Block.Tables
import YM.Comparison.RG02.Bare.Signals
import YM.Comparison.RG02.Step.History
import YM.PertExtension.BareWords
/-!
# Explicit initialization of the local comparison, same bare stencil columns/valuations

(In LocalFormal frame, i.e., full periodic path regulator.) Does not assert measures
 are the same between periodic and inversion regulators. Full marked numerator
 and normalized & log outputs of an actual step computed when varying g (the bare
 link coupling including in the block penalty S, NOT changing other level data). Tree-independence
 & kernel comparison with costs at *fixed* finite regulator `Bare.header` using
 TRUE likelihoods and Haar and physical stencils instead of local moments or mask
 competitors. Pointwise-held A, no facts here about integration against a coarse
 measure. These FULL group integral expansions are proved **at the top step**
 (`cutoff=i+1`); for general Bulk.Colors at older levels see `bridgeAll` for
 comparison of germs and `Comparison.RG02.Laplace.find` for aperture-only
 expansions. No moving-cutoffs assertion about these expansions.

 As everywhere `poster`/`element` is real even before integration. Literals
 can be accessed at an admissible horizon and on a coherent physical trajectory
 of section data. These are same regulator units (keep a^{-h}/volume factors
 external vs pricing etc). These formulas give the RG10 side using arbitrary
 mark placements (even equal physical points, no singular analysis asserted).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Block
open Lattice Wilson Exterior Tree Precision RG MeasureTheory
open Comparison.RG02 FormalOPE.RG10 Marker Multi PowerSeries
open Function Filter Finset PertExtension PertExtension.Series PertExtension.Series.Tested
open PertExtension.Orb.SlotEvaluation PhysicalNext.Repeat.Legato Integration
open Comparison.RG02.Laplace Integral
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}(T:Run G)(i u :ℕ)
local notation "ℱℱ" => T.family
local notation "Γ"=> RunFormalChain.fromRun T
set_option quotPrecheck false
local notation "K"=> (Γ).step (i+1) i u (Nat.lt_succ_self i)
local notation "n"=> (ℱℱ).side (i+1) u
local notation "L_" h:max => T.family.labels.level h
local notation "S"=> T.family.path.levels.clock.op i u
variable {V:Type}[Fintype V][DecidableEq V] {R:Census V}
lemma bridgeAll (D:LocalFormal.Datum ℱℱ R)(k r:ℕ)(hk:k≤r)(s:R.Mode):
   let A:=D.kernel Γ; let W:=D.colors; let F:=D.forest; let t:=D.tag;let B:=D.field;
   let I:=naked A F t; let O:=action A F t B W; let X:=columns A F B W
   I.markedFunded O X ∧ Order.series R r (I.close O X)= D.ordinary Γ r∧
   Order.series R r (I.contraction O X)=D.markedLog Γ r ∧
   LocalFormal.runCoefficients T D r k s= coeff k (Word.see s (I.close O X)):= by
    intro A W F t B I O X; have he:= positive_normalization A F t B W r
    refine ⟨ pays A F t B W,he, positive_marks A F t B W r,?_ ⟩
    change (Order.observe R r (D.ordinary Γ r) k).part s=_; rw [←show _=D.ordinary Γ r from he]
    rw [Order.observation _ _ _ hk,Word.unfold_see]
lemma clothes : ∀ d:ℕ,Bid.pop (T.family.localSection d):= fun d=> Next.Foundations.valuation G d
variable (R)
variable (x: V→ Site (T.family.side (i+1) u))(d:V→ℕ)(v:(j:V)→(T.family.labels.level (d j)).Index)
abbrev element (j:V):= fieldAt (T.family.localSection (d j)) (v j) (x j)
def depths (j:V):= ((L_ (d j)).grades (v j)).2
-- independent of formal-order. ordinary powers of g. 
def ink : Bulk.Colors R G n:= Bare.Signals.flare R (fun j _ z => ((element T i u x d v j z:ℝ):ℂ)) (depths T d v)
def wardrobe:= Bare.bareUp R (H:=T.family.path) i u (ink T i u R x d v)
local notation "W"=> wardrobe T i u R x d v
local notation:max "O_" j:max=> element T i u x d v j
local notation:max "l_" j:max => depths T d v j
local notation "P"=> T.family.path.rep (i+1) u (i+1)
local notation "Q"=> T.family.path.rep (i+1) u i
lemma earns : let W':=ink T i u R x d v; Bulk.Well W' ∧ Bare.Starts W':=by
    let O (j:V): Config G n→ℂ := fun z=> ((O_ j z:ℝ):ℂ)
    have hz (j:V) : O j= (T.family.localSection (d j)).places (Pi.single (v j) 1) (x j):= funext fun U=> scalar_real (T.makes.sections _)
    have ht (j:V): Continuous (O j) := hz j ▸ (T.family.localSection (d j)).continuous_places _ _
    -- orientation ▸
    have hb (j:V): Envelope (O j) := Envelope.compactC (ht j)
    intro W'
    refine ⟨ Bare.Signals.flare_well R (fun j _=> O j) _ ?_ (fun j _=> hb j) ?_, Bare.Signals.flare_good _ (fun j _=>O j) _ ?_⟩
    · intro j; rw [hz]; exact Assembly.GradeAt.coarse (g:=(Prod.snd:ℝ × fieldDir G n 1→_)) (Bare.Signals.primary (C:=T.family) (v j) (clothes T (d j)) (x j)) contDiffAt_snd rfl
    · intro j _; rw [hz]; exact (T.family.localSection _).placed_invariant (T.makes.sections _) _ _
    intro j; obtain ⟨M,hM⟩:= (hb j).cost; refine ⟨0,max 0 M,le_max_left ..,?_⟩; exact Eventually.of_forall (fun _ U=> by rw [pow_zero,mul_one]; exact (hM _).trans (le_max_right ..))
lemma dressedTop : (W).Standard ∧ Bare.Witnessed W K := let h:= earns T i u R x d v;⟨Bare.still_ok _ Γ _ _ _ h.1, Bare.based _ Γ _ _ _ h.1 h.2 ⟩
variable (F:Forest (T.family.path.levels.clock.op i u).ratio)(t:(T.family.path.levels.clock.op i u).Choices)(B:fieldDir G (T.family.side i u) 1)
def ticket : LocalFormal.Datum T.family R:= ⟨i+1,u,i,Nat.lt_succ_self _,F,t,W,B⟩
local notation "D"=> ticket T i u R x d v F t B
local notation "ρ" => Bare.realMoment K F W t B
-- includes weaving office scalar, step likelihood ALL tags. full. `rho` plays conditional unmarked leading log; normalized field A lives at gauge B.
lemma read_step (k:ℕ): Fleet.Test ((D).raw Γ k) ρ ∧ Trial (detail ((D).vacuumLog Γ k) R.quiet) (fun g=>Complex.ofReal (Real.log (Bare.rho K F t B g))) k∧ Fleet.Test ((D).ordinary Γ k) (Order.unitScale ∘ ρ)∧ Fleet.Test ((D).markedLog Γ k) (Extra.Trajectories.connected ∘ Order.unitScale ∘ ρ):=Bare.wilson_step_test K F W t B k (T.family.path.levels.budget i) (dressedTop T i u R x d v).2
lemma determines (k r:ℕ)(hk:k≤ r)(s:R.Mode)(a:ℕ→ℂ)(h:Trial a (fun g=> (Order.unitScale (ρ g)).part s) r):
   LocalFormal.runCoefficients T D r k s= a k:= trial_gap ((read_step T i u R x d v F t B r).2.2.1 s) h k hk
lemma fullMarked (g:ℝ)(U:Config G n)(s:R.Mode): (Bare.top W g U).part s=
   (↑(Wilson.bare (temperature g) U):ℂ)* ∏ j∈s.val,((g ^ l_ j)⁻¹:ℝ) • (Complex.ofReal (O_ j U)):=by
   unfold Bare.top; rw [Poly.part_smul]; congr 1;
   unfold Bare.Passes; rw [show markedLog g U W= markedLog g U (ink T i u R x d v) from rfl, ink,Bare.Signals.singleton,Cumulants.pass_lambda]
-- hence exactly same as actual stencil columns repriced at this regulator at this γ.
-- No horizon or power varying with the later formal order!
omit [Fintype V] [DecidableEq V] in
lemma actualMarks (g:ℝ)(j:V): let c:= (g ^ l_ j)⁻¹; let w: (L_ (d j)).Coeff:= (↑c:ℂ) • (Pi.single (v j) 1 : (L_ (d j)).Coeff)
   T.family.O (i+1) u (d:=d j) (SameColumns.reprice T.family (i+1) u w) (x j)= c • (Complex.ofReal ∘ O_ j):= by
    intro c w; rw [SameColumns.reprice_eq]; funext U; dsimp only [Pi.smul_apply,Function.comp_apply,w]; rw [show Complex.ofReal (O_ j U)=(T.family.localSection (d j)).places (Pi.single (v j) 1) (x j) U from scalar_real (T.makes.sections _)]; unfold Source.SectionData.places; rw [(T.family.localSection _).eval_linear.map_smul]; rfl
local notation "g'"=> Pert.Asymptotics.regulatorRun ℱℱ (i+1) u (i+1)
local notation:max "o_" g:max => office K F t g 0 B
-- literal SAME Family.beta.
lemma officeAt : temperature g'= (P).beta ∧ Bare.rho K F t B g'= (o_ g')⁻¹ * (Q).eval (sample g' B):=by
    have h:= Local.RealStep.trajectory T.family (i+1) u (i+1) T.makes le_rfl
    refine ⟨h,?_⟩; unfold Bare.rho; rw [h]; rw [show (Q).eval=(S).push (P).beta (P).eval from (T.makes.wilson.steps (i+1) u _ (Nat.lt_succ_self i)).1, show (P).eval = Wilson.bare (P).beta from (T.makes.wilson.starts (i+1) u).2]
end YM.FVAAlt2.Block
