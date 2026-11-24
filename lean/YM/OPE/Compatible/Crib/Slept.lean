import YM.OPE.Compatible.Crib.Fable
/-! # geometric stencils for locality. within torus from O∞. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n c f:Side} {b i k r m:ℕ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph
open Spells
variable (S:StepData c f)(H:Odd S.ratio.count.val)(o:Site f)
local notation "Fθ"=> forest S.ratio H
local notation "Yr"=>AxisChart G Fθ
noncomputable abbrev letter (G:Gauge):AxisChart G Fθ→L[ℝ] Bid.Dir G f:= ribz S H ∘L ContinuousLinearMap.inr ℝ (Bid.Dir G c) (AxisChart G Fθ)
noncomputable abbrev ath(Y:Yr):=charW o (letter S H G Y)
lemma plaqueU (x: Yr)(p:Edge (Site f)): letter S H G x (p.1,coord p.2)= YM.Stationary.edgeColor (YM.Stationary.pad Fθ x) p := rfl
noncomputable abbrev crux (b:ℕ): Seats Fθ:=Finset.univ.filter fun x:(Fθ).Free=> ∃ i:Dim o (4*b), x.val=i.val
noncomputable def rip (G:Gauge)(I:Seats Fθ) : AxisChart G Fθ→L[ℝ] (Libra.Keys G (↥I)):= ContinuousLinearMap.pi (fun i:(I:Type)=> ContinuousLinearMap.proj (φ:=fun _:(Fθ).Free=>G.Color) (R:=ℝ) i.val)
lemma veil (I:Seats Fθ)(x:Yr) : ‖rip S H G I x‖≤ ‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun p=> norm_le_pi_norm x p.val
section
local notation "Ix"=> crux S H o b
local notation "Rx"=> rip S H G Ix
lemma ReadIx (p: Yr)(y:TilesB (4*b)): InLine (4*b) (ath S H o p) y= letter S H G p ((Spindle.reads y o).val.1,coord (Spindle.reads y o).val.2):=by
       ext i; change (letter S H G p) (o+wrap f y.val.1,coord y.val.2) i=(letter S H G p) (wrap f y.val.1+o,coord y.val.2) i; rw [add_comm]
lemma woodK (p:Yr) : ‖InLine (4*b) (ath S H o p)‖ ≤ ‖Rx p‖:=by
       apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; rw[ReadIx,plaqueU]; let a: Dim o (4*b):= Spindle.reads i o; by_cases h:a.val∈(Fθ).trunks
       · rw [show YM.Stationary.edgeColor (YM.Stationary.pad Fθ p) a.val=0 from YM.Stationary.pad_trunk Fθ _ ⟨_,h⟩,norm_zero]; exact norm_nonneg _
       let u:(Fθ).Free:=⟨_,h⟩; rw [show YM.Stationary.edgeColor (YM.Stationary.pad Fθ p) a.val=p u from YM.Stationary.pad_free Fθ p u]; exact norm_le_pi_norm (Rx p) ⟨u, mem_filter.mpr ⟨Finset.mem_univ _,⟨a,rfl⟩⟩⟩
lemma ψquick (x:Yr): InLine (4*b) (ath S H o (stake Ix (Rx x)))= InLine (4*b) (ath S H o x):=by
       funext i; rw [ReadIx, ReadIx, plaqueU,plaqueU]; let j:= Spindle.reads i o; by_cases h: j.val∈ (Fθ).trunks
       · exact Eq.trans (YM.Stationary.pad_trunk Fθ _ ⟨_,h⟩) (YM.Stationary.pad_trunk Fθ _ ⟨_,h⟩).symm
       let p:(Fθ).Free:=⟨_,h⟩; let q: (Ix:Type):=⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,rfl⟩⟩; change YM.Stationary.edgeColor (YM.Stationary.pad _ (stake Ix (Rx x))) p.val= YM.Stationary.edgeColor _ p.val; rw [YM.Stationary.pad_free,YM.Stationary.pad_free]; exact stake_on Ix q _
lemma vents (p q:fieldX (Shade G))(hx:InLine (4*b) p= InLine (4*b) q):BFilm b p=BFilm b q:=by
       have ht(i:ℕ): PlateB i b p=PlateB i b q:=by
            funext j; change WardBin.leading i (sheetM (pealB j) p)=WardBin.leading i (sheetM (pealB j) q); rw [volt p q hx j]
       unfold BFilm; rw [ht,ht,ht]
lemma offX (x:Yr): BFilm b (ath S H o (stake Ix (Rx x)))=BFilm b (ath S H o x):=vents _ _ (ψquick ..)
end
end YM.OPE.Crown
