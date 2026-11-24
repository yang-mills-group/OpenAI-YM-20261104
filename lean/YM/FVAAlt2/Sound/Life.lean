import YM.FVAAlt2.Sound.Ethos
import YM.FVAAlt2.Rocket.Main
/-!
# Moving schedules for PER history -> COVER projection -> specified MS reference
Apply the fixed-regulator (Inversion gauge) identities, real Peal solution.See Top, IR Ledger budgets, and MS removal *after* coefficient algebra of SCALLED kernels. Thus no leftover multiplication by bare Price factors without showing sufficient rate. Here first full moving-history placement supplier. Regular torus is separate from inverted top side. Entirely formal result, but uses authentic Run, Bare labels and the prescribed germs of Local.Fk algorithms. Not an OPE claim. Terminal orientation.Delta for turning these post-adjustment reports into canonical real frames still requires horizon hypotheses or its own theorem, e.g. if using exact position determinant data on these varying tracks. Top.Output done for fixed-q regulators there (different kernel propagation and estimates). 

When decorating with convergence statements we can quantify over ANY position profiles in scope of `Profile,Mesh,Venue`. Includes varying-point asymptotics via the abstract filter & `visual` corollary at each separated tuple, admits every finite-budget extension of ℓ(x) each x. This is existential for lower bound, but at all larger periods and at *multiplicative-correction prices*, and same cost inequalities (not just says a period trajectory exists for each ℓ-position). No exponential-coefficient estimate in the periodic side λ, in particular cannot use if insisting on a secondary period upper bound. `comparisonOps` outputs the comparison on the **formal side** `MS_Data` cutoff scheme. (Then Top.CheckG applies to MS comparison with RG10 perturbative Pub; this file is its supplier, explaining where the inputs come from using the Run and normalization `adjust`; not claiming here that final real-frame multiplicative operations have been applied to local material.) -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Sound
open Function Set Filter MeasureTheory Real Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field
open MS MS.Land MS.Dial MS.Rake MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open Figure
open PowerSeries Integration RunFormalChain FormalOPE Pipeline Pipeline.See
open YM.FVAAlt2
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(hG:G.Simple) {K:KernelChoices} {I X:Type} [Fintype I] [LinearOrder I]
variable (Y:Oracle.Program K)(Z:∀ B:Patch,B.Branches K G) (C:Run G)(R:Lodge.Contract C Y Z)
set_option quotPrecheck false
variable (t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x)
local notation "B"=> (R.profile Y Z C t ht)
local notation "P"=> (Period.Field.LodgeT.instance_real Y Z C R t ht) -- period. 
variable (F:Calibration.Tent ( (R.profile Y Z C t ht).entire )) {g:G.ColorIndex} (p d:ℕ)
variable {u:MS.Local.Physical.Deck G} (D:I→ MS.Rake.Label u) (T:MS.Land.Prescription u) {J:Booked u}(H: MS_Data G J)
variable (l:Filter X)(μ:ℝ)
local notation "M"=> (B).Θ
local notation "θ"=> (fun x=>μ-(B).Θ x)
def Alone (W:Lodge.Track X)(x:X):= exp (-(W.Θ x))
def BudgetAir (W:Lodge.Track X)(i:X) := exp ( - MS.Tide.mildG * W.Θ i )
local notation "ε"=> (Alone (B))
variable (Λ:X→ℕ)
abbrev Margin:= Ethos.Asked Y C Z (P) F T (B).stop (fun x=>μ - (R.profile Y Z C t ht).Θ x) (Alone (B)) (Ethos.tot (B)) d p (BudgetAir (B)) I Λ -- holes Track
variable (a:X→ Cover)(w:I→ X→ Cover)
local notation "V!"=> (B).PoseT μ a w
local notation "z"=> ( Rocket.Zpose V! )
def prospect (j:ℕ)(i:X): ℂ:= coeff j ( Figure.runPer C Z (Period.Field.LodgeT.instance_real Y Z C R t ht) ( Rocket.Zpose ((R.profile Y Z C t ht).PoseT μ a w) ) (sheet F) (Λ i) ( B ).stop D T (μ-( B ).Θ i) (Alone (R.profile Y Z C t ht) i) i )
lemma guards : ∃ σ:X→ℕ, Margin (I:=I) Y Z C R t ht F p d T μ σ := Ethos.served C Z Y P F T ( B ).stop θ ε (BudgetAir _) d p (Ethos.tot (B)) fun _=> exp_pos _ -- order ht?
variable (h:Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p)(Hq:∀ x,p≤t x)(hV:Tendsto t l atTop)
variable (hver:(R.profile Y Z C t ht).VenueT a)(hp:MS.Tide.Profile ((R.profile Y Z C t ht).PoseT μ a w).profile w)(he:Rake.Mesh ((R.profile Y Z C t ht).PoseT μ a w).profile ( Fleet.info w ))
variable {σ:X→ℕ} (hσ:Margin (I:=I) Y Z C R t ht F p d T μ σ)(hx:∀ᶠ x in l, σ x ≤ Λ x) (hd:∀ i:I,( D i ).h ≤ d) (hT: TaylorOKPl H (Lobby.Table (basisR C) u) T)
include hV hver hp hσ hx hd
lemma further (j:ℕ)(hj:j≤p) : PeakT l (V!).profile mildG ( ( Sound.prospect Y Z C R t ht F D T μ Λ a w j ) - ( Lodge.physicalCover Y Z C R t ht F μ D a w T j )):= by
 refine ⟨1,one_pos,?_⟩; filter_upwards [ Ethos.eventuallyIn (W:=w) hver hp (R.batch_r Y Z C t ht hV), hx ] with x hm hx; rw [one_mul]; exact hσ.answers x (Λ x) hx D hd z hm j hj
include hG h Hq hT he
lemma finalT (j:ℕ)(hj:j≤p): PeakT.twin l (V!).profile mildG ( Sound.prospect Y Z C R t ht F D T μ Λ a w j ) ( fun i:X=> Dial.tour H D μ (testP V! i) Finset.univ j ):=by
    obtain ⟨hK,hA⟩:= Lodge.narrated Y Z C R t ht F μ p D h hG hV Hq hT a w hver hp he j hj
    refine ⟨hK,?_⟩; have hu:= ( PeakT.plus (further Y Z C R t ht F p d D T l μ Λ a w hV hver hp hσ hx hd j hj ) hA ); rwa [sub_add_sub_cancel ..] at hu
lemma tends (f:I→QP)(hf:Injective f) (hw:Tendsto (testP V!) l (𝓝 f))(j:ℕ)(hj:j≤p): Tendsto (Sound.prospect Y Z C R t ht F D T μ Λ a w j) l (𝓝 (Dial.tour H D μ f Finset.univ j)) := by
    obtain hu:= finalT hG Y Z C R t ht F p d D T H l μ Λ a w h Hq hV hver hp he hσ hx hd hT j hj; exact Dial.agrees V! hu ((B).θ_runs (R.batch_r Y Z C t ht hV) ) ( ( Dial.contin H D f hf Finset.univ j μ ).1.tendsto.comp hw )
omit hp he
lemma visual (f:I→QP)(hf:Injective f)(j:ℕ)(hj:j≤p): Tendsto (Sound.prospect Y Z C R t ht F D T μ Λ a ((B).video f) j) l (𝓝 (Dial.tour H D μ f Finset.univ j)):=by
    obtain hh:= R.batch_r Y Z C t ht hV; let hc:=( B ).useful a μ f l hver hf hh; exact Sound.tends hG Y Z C R t ht F p d D T H l μ Λ a (( B ).video f) h Hq hV hver hc.total hc.knit hσ hx hd hT f hf ( ( B ).comeback a μ f l hh hf ) j hj
end YM.RegulatorIR.FVAAlt2.Sound
