import YM.Juniper.Cinch.Binding
import YM.UVExtension.Yard.Branch
/-!
 # After winding-correction numerical transport; an actual E certificate for the ONE output.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open Quotes Geo Ovens Ovens.Pipes Progress.DirectedRecipe Payments Further.LogJets Pressure UVExtension UVExtension.Yard UVExtension.Lamppost UVExtension.Concert
open Extra.Iteration Song
open scoped Classical Topology BigOperators ContDiff InnerProductSpace
set_option quotPrecheck false
variable {G:Gauge}{W:BudgetPoint}{c:Side}{δ ε b v w τ σ t u : ℝ}(T:Pylon W c)
variable {Y: Listing G c} {f g : Collection.Source G c} {α r Δ η φ Λ θ : ℝ}
   {R:PathData G}{clip:Clip}(hG:G.Simple)(hw: Geo.Width W clip σ)(hv:R.Bounds clip σ φ Λ)(hf:WilsonStartup.Decent clip W) (hu: W.threshold^2 * |Δ-δ| ≤ b)
  (hk:20<c.val)
local notation "Λ'"=> shelves Y R W
local notation "δ'"=> (Averaging.delta (Y.read f) - Δ)
local notation "X'"=> adobe Λ' T
local notation "F"=> Collection.fill Y R clip W f α Δ
local notation "F'"=> flint T δ' F
local notation "G'"=> Collection.fill Y R clip W g α δ
local notation "C"=> forecastW G c W δ'
local notation "d"=> regularNeed G W clip σ φ 0 b
local notation "q"=> softNeed G W clip σ φ 0 b
local notation "N"=> badge c

def paper (g:Collection.Source G c)(Y:Listing G c)(R:PathData G)(S:Clip)(a δ:ℝ) := flint T 0 (Collection.fill Y R S W g a δ)
local notation "g'"=> paper T g Y R clip α δ
def shade (p k: Ovens.Tap G c) : Ovens.Tap G c := ⟨p.regular-k.regular,0,p.logarithm-k.logarithm⟩
local notation "Z"=> shade F' g'
local notation "Φ"=> Collection.fill Y R clip W (f-g) 0 (Δ-δ)
variable (hu' : smoothP W Y.reg f.logRead) (hr: smoothP W Y.reg g.logRead)
include hG hw hv hf hu
lemma honest (he: Meadow.Budget W Y.reg (f-g).logRead b) : ((Λ').pours Φ).EBound W d ∧ ∃ k:ℕ→ℝ,softCost W (Λ') k q∧∀ i U, ‖(Φ).logarithm i U‖≤ k i:= by
   obtain ⟨k,hk,h⟩:=he; have he i:=(h i).2; have hh (i:ℕ):=(h i).1
   obtain ⟨hu,hv⟩:= Collection.Local.quote_family hv hf hw 0 (X:=Y) (u:=k) (Δ-δ) he hk hu -- :: adjust
   have hX(i :ℕ):= Collection.Local.quote_soft (R:=R) (c:=clip) hG 0 (Δ-δ) he hh (numbering (Collection.LKey c) i)
   exact ⟨⟨_,fun i=> Collection.Local.quote_regular hG ‹R.Bounds clip σ φ Λ› hf 0 (Δ-δ) he hh (numbering _ i),fun i=>Cost.equiv (numbering _) (hu i)⟩, quoteL R W clip 0 (Δ-δ) k ∘ numbering _, ⟨fun i=> (norm_nonneg _).trans (hX i 1),fun i=>Cost.equiv (numbering _) (hv i)⟩, fun i U=> hX i U⟩
include hu' hr
lemma harvestE (he: Meadow.Budget W Y.reg (f-g).logRead b) : ((X').pours Z).EBound W (d+C) ∧ ∃ k:ℕ→ℝ,softCost W X' k (q+C)∧∀ i U, ‖(Z).logarithm i U‖≤ k i:= by
   let p:= shade F' g'; let p':= flint T δ' Φ; let z:=δ'; let D:=(f-g)
   have hg(i:Gains c)(u:Config G c): spread ((F).regular) (Pylon.gap z) i u- spread ((G').regular) (Pylon.gap 0) i u= spread ((Φ).regular) (Pylon.gap z) i u∧ spread ((F).logarithm) (Pylon.graft T z) i u- spread ((G').logarithm) (Pylon.graft T 0) i u=spread ((Φ).logarithm) (Pylon.graft T z) i u := by
       cases i
       next i=> exact ⟨congr_fun (archive_sub hu' hr R α Δ δ (numbering (EKey c) i)) u,Collection.throws_sub hu' hr R α Δ δ (numbering _ i) u⟩
       next i=> simp [spread,Pylon.gap,Pylon.graft,twill,masked, Set.indicator]
   have hpX: (p).regular=p'.regular:= funext fun i=> funext fun T=> (hg (N i) T).1; have hScope:(p).logarithm=p'.logarithm:= funext fun i=> funext fun T=> (hg (N i) T).2
   obtain ⟨ha,k,hK,hL⟩:= honest hG hw hv hf hu he
   obtain ⟨x,hx,hv⟩:= Cinch.fledged Λ' T z ha
   refine ⟨⟨x,fun i=>?_,hv⟩,_,Cinch.soften Λ' T δ' k hK,fun i U=>?_⟩
   · rw [show ((X').pours Z).E i = p'.regular i from congr_fun hpX i]; exact hx i
   rw [show (Z).logarithm _ _= _ from congr_fun (congr_fun hScope i) U]
   let q'(i':Gains c):=Sum.elim k (fun _ => Pylon.droop G W z) i'; change ‖spread ((Φ).logarithm) (Pylon.graft T z) (N i) U‖≤ q' (N i); cases N i; exact hL _ U; exact Pylon.vessel T z _|>.2 U
end YM.Juniper.Cinch
