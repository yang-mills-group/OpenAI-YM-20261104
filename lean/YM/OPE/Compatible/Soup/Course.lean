import YM.OPE.Compatible.Soup.Pine
import YM.OPE.Compatible.Soup.Pillar
/-!
# At the actual hill. Budgets across arbitrary families
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(h:Tendsto β φ atTop)
noncomputable abbrev Mater (j:I):= (A j).lens.ℳ
noncomputable abbrev Haslt (j:I):= (Mater A j).live
noncomputable abbrev DialK (j:I):=(A j).lens.fees
noncomputable abbrev WorkB (j:I):= Mnd i S A j+1
noncomputable abbrev Stru (j:I):= (A j).path
noncomputable abbrev Meta (j:I):=(A j).path.p
noncomputable abbrev et (j:I):=Clock.gap (A j).path.beta
noncomputable abbrev Sez : Prop :=∀ i:I, Board (n i) (WorkB A i+1)  -- may Prop fine
variable (U: Scaffold φ (Counters β) n (Mnd i S A) r)
lemma capB (j:I): (Mater A j).clip=S.clip:= (A j).lens.clip
lemma trueB (j:I): (Stru A j).clip=S.clip:= (A j).gen.clip
lemma gaugesK (j:I): (Stru A j).path=Haslt A j := (A j).valid.path
lemma funB (j:I): 0≤ DialK A j:= zero_le_one.trans (A j).lens.positive
lemma Walt (j:I): (Haslt A j).Bounds S.clip S.width S.paths (DialK A j):=by
        rw [← gaugesK]; change (A j).path.path.Bounds _ _ _ _; rw [← trueB A j, show DialK A j= _ from (A j).salaryF]; exact (A j).gen.lawful.paths
include h
local notation "L♦"=> (carth h)
lemma MintW : Receipt β φ (fun j=> (WorkB A j:ℝ)):=by unfold WorkB;push_cast; exact (Asc_more i S A h).plus (YM.OPE.Score.steady _ (carth h)) (carth h)
lemma mUses : Wax β φ (DialK A) 0:= ((CoinS h τ).pays (carth h)).congr (Eventually.of_forall fun i=>(A i).salaryF.symm)
lemma Squater (s:ℝ): Receipt β φ (fun j=> Squad (WorkB A j) s):=by
       unfold Squad; let t(c:ℝ): Receipt β φ (fun _=>c):=YM.OPE.Score.steady c (carth h); exact (((t 2).product ((MintW A h).plus (t _) (carth h))).power 4 (carth h)).product (t _)
omit h
open Merchant.SiteL
noncomputable abbrev Punched (j:I): Board (n j) (r+1):= (U.top.room j).money
noncomputable abbrev WickH:=WorkB A
include U in lemma Volta (j:I): Board (n j) (r+2):=tip (U.bone j) (show r+2 ≤ _ from by have hx :r< WorkB A j:=(U.top.room j).wide; unfold WorkB at *; omega) -- Lean ambiguity
include U in lemma broader (j:I):r+1 ≤ WorkB A j:= (U.top.room j).wide
local notation "W!"=>Merchant.Chamber G r
noncomputable abbrev Fract (S:Stage)(r:ℕ):ℝ:=2* Merchant.damp r S.clip
lemma Fractage (S:Stage)(r:ℕ): 0 < Fract S r:=mul_pos (by norm_num) (Merchant.dampK _ _)
variable (D:I→ Law (Merchant.Chamber G r))
noncomputable abbrev KPole (j:I):= Variance.Dune (n:=n j) (Mater A j)
noncomputable abbrev LPole (j:I):= Variance.Rh (n:=n j) (Mater A j)
noncomputable abbrev Stair (j:I) := sailT G (Punched A U j)
structure GaugeD : Prop where
        obey (j:I): SiteL (Stair A U j) (chrom (KPole A j)) (D j)
        rate (j:I) (x: Merchant.Chamber G r): Fract S r * ‖x‖^2 ≤ (D j).P x x
section
variable {A U D} (π:GaugeD A U D)
-- yearly dispatches.Poses
structure MintL (f g:I→ℝ):Prop where
        meat : Receipt β φ f
        lite : Wax β φ g 0
        fare (j:I): 0 ≤ f j∧ 0 ≤ g j
        ν (j:I) (x:Bid.Dir G (n j))(he:SerT x (WorkB A j))(v:ℝ)(hv:‖x‖ < v): Past (KPole A j) x 5 v (f j)∧Past (LPole A j) x 5 v (g j)
-- manufacture
variable (A U D)
include h
lemma merit :∃ f g,MintL (A:=A) (φ:=φ) f g:=by
        obtain ⟨f,s,t,hf,hs,ht,H⟩:=perch_kind (k:=5) (i:=i) (T:=T) S.clip S.width_pos S.paths_pos.le; let p(j:I):=Squad (WorkB A j) s; refine ⟨fun j=>f*p j,fun j=> t*DialK A j*p j,?_,?_,fun j=>?_,fun j x he v hv=>?_⟩ -- struct
        · exact (YM.OPE.Score.steady _ (carth h)).product (Squater A h _)
        · exact ((((RateLE.const (t:ℝ) (carth h)).mul (mUses A h)).mul (waitG h (Squater A h _))).mono (by norm_num))
        · exact ⟨mul_nonneg hf (squad_pos ..),mul_nonneg (mul_nonneg ht (funB A j)) (squad_pos ..)⟩
        exact H (n j) (Meta A j) _ _ _ (Mater A j) (capB A j) (Walt A j) (WorkB A j) x he hv
omit h
noncomputable def tapP (j:I):= pour (Stair A U j) (chrom (KPole A j)) (D j)
noncomputable abbrev mixT(j:I) := mate (Stair A U j) (chrom (KPole A j)) (D j)
end
end YM.OPE.Owl.HillZ
