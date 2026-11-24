import YM.OPE.Compatible.Mould.Sap
/-!
# Stem extension.Killer lift -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J}{w:ℝ}{D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full
variable {p₁:Clip}{u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(L:Lance X)
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
local notation "F!"=>Tracts G d τ
local notation "D!"=>Topic.Dross Hp Z a e
lemma phiSub (x y:Mint Z e)(he:e<l+1)(i:Phase) : UΦ Z he (x-y) i=UΦ Z he x i-UΦ Z he y i:=map_sub ((Drift.Turns D₀ i).Tap e) _ _
private lemma phase_limit {he : e < l+1} (z : Mint Z e) (i : Phase)
    (hg : LimitQ (UΦ Z he z 0) r) : LimitQ (UΦ Z he z i) (if i=0 then r else e+1) := by
  by_cases hi : i = 0
  · subst i
    exact if_pos rfl ▸ hg
  · rw [if_neg hi]
    intro m hm
    omega

private lemma cut_head {he : e < l+1} (Y : M → Submodule ℝ (Tracts G d τ)) (hx : HostE e ν U Y)
    (p : M → Mint Z e) (i : Phase) (hy : Wealth (fun j => (p j).val) u ν)
    (hm : ∀ j, UΦ Z he (p j) i ∈ Ghost G l e) (hg : ∀ j, LimitQ (UΦ Z he (p j) 0) r) :
    ∃ v : ∀ j, U.flag e j, Wealth (fun j => (v j).val) u ν ∧ ∀ j, (v j).val ∈ Y j ∧
      Crop (if i=0 then r else e+1) (v j).val ∧ tag D₀ e (v j).val = UΦ Z he (p j) i :=
  hx _ _ (cashU he p hy i) (fun j => ⟨hm j, phase_limit (p j) i (hg j)⟩)

private lemma cut_residual {he : e < l+1} (i : Phase) (p z : Mint Z e)
    (hp : trims i.val p.val) (hz : trims i.val z.val) (hi : UΦ Z he p i = UΦ Z he z i) :
    trims (i.val+1) (p-z).val := by
  apply (bridgeV Z (i.val+1) i.isLt he _).2
  intro k hk
  by_cases heq : k = i
  · subst k
    rw [phiSub]
    exact sub_eq_zero.mpr hi
  · have hpre : trims i.val (p-z).val := trims.sub hp hz
    exact (bridgeV Z i.val i.isLt.le he _).1 hpre k
      (Nat.lt_of_le_of_ne (by omega) (fun h => heq (Fin.ext h)))

private lemma crop_shifted (h : Aware d τ) {x y : Tracts G d τ} (i : Phase) (hy : y = Shifts G h i x)
    (hc : Crop (if i=0 then r else e+1) x) (ht : trims i.val y) : Crop r y := by
  by_cases hi : i = 0
  · subst i
    rw [hy]
    change Crop r x
    rw [if_pos (rfl : (0 : Phase) = 0)] at hc
    exact hc
  · exact Crop.from (ht (0 : Phase) (Fin.pos_iff_ne_zero.mpr hi))

private lemma cut_entry {he : e < l+1} (j : M) (i : Phase) (p : Mint Z e) (v f : U.flag e j)
    (hp : trims i.val p.val) (hf : f.val = Shifts G D₀.aware i v.val)
    (hc : Crop (if i=0 then r else e+1) v.val) (hv : tag D₀ e v.val = UΦ Z he p i)
    (hr : UΦ Z he (U.read e he j f) i = UΦ Z he (U.read e he j v) 0) :
    trims i.val f.val ∧ Crop r f.val ∧ trims (i.val+1) (p-U.read e he j f).val := by
  have htrim : trims i.val f.val := hf ▸ trimS v.val i D₀.aware
  have hmatch := hr.trans ((discU he j v).trans hv)
  exact ⟨htrim, crop_shifted D₀.aware i hf hc htrim,
    cut_residual (Z := Z) (he := he) i p (U.read e he j f) hp (U.quake e he j f i htrim).2.1 hmatch.symm⟩

private lemma finish_cut {he : e < l+1} (Y : M → Submodule ℝ (Tracts G d τ))
    (p : M → Mint Z e) (i : Phase) (hn : ∀ j, trims i.val (p j).val)
    (heads : ∃ v : ∀ j, U.flag e j, Wealth (fun j => (v j).val) u ν ∧ ∀ j, (v j).val ∈ Y j ∧
      Crop (if i=0 then r else e+1) (v j).val ∧ tag D₀ e (v j).val = UΦ Z he (p j) i)
    (shift : ∀ v : ∀ j, U.flag e j, Wealth (fun j => (v j).val) u ν → (∀ j, (v j).val ∈ Y j) →
      ∃ f : ∀ j, U.flag e j, Wealth (fun j => (f j).val) u ν ∧ (∀ j, (f j).val ∈ Y j) ∧ ∀ j,
        (f j).val = Shifts G D₀.aware i (v j).val ∧
        UΦ Z he (U.read e he j (f j)) i = UΦ Z he (U.read e he j (v j)) 0) :
    ∃ f : ∀ j, U.flag e j, Wealth (fun j => (f j).val) u ν ∧ (∀ j, (f j).val ∈ Y j) ∧ ∀ j,
      trims i.val (f j).val ∧ Crop r (f j).val ∧ trims (i.val+1) (p j - U.read e he j (f j)).val := by
  obtain ⟨v, hw, hs⟩ := heads
  obtain ⟨f, hfw, hfs, hfr⟩ := shift v hw (fun j => (hs j).1)
  exact ⟨f, hfw, hfs, fun j => cut_entry (Z := Z) (U := U) (he := he) (r := r) j i (p j)
    (v j) (f j) (hn j) (hfr j).1 (hs j).2.1 (hs j).2.2 (hfr j).2⟩

include L T'

private lemma cut_ghost {he : e < l+1} (p : Mint Z e) (i : Phase)
    (hF : p ∈ Topic.Dross Hp Z a e) (hn : trims i.val p.val) : UΦ Z he p i ∈ Ghost G l e :=
  Nem Hp Z a he T'.dimD T'.cap T'.vol p i hF hn L

set_option maxHeartbeats 200000 in
lemma stepCut {he:e< l+1}(hx:HostE e ν U (Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)))(p:M→Mint Z e)(hy: Wealth (fun i=>(p i).val) u ν)(i:Phase) (hn:∀ m,trims i.val (p m).val)(hF:∀ i,p i∈ Topic.Dross Hp Z a e)(hg:∀ j,LimitQ (UΦ Z he (p j) 0) r) :∃ f:∀ j,U.flag e j, Wealth (fun j=>(f j).val) u ν∧(∀ j,(f j).val∈ S! j)∧∀ j,trims i.val (f j).val ∧Crop r (f j).val∧ trims (i.val+1) (p j-U.read e he j (f j)).val :=by
  apply finish_cut (Z := Z) (U := U) (ν := ν) (he := he) (r := r) (S!) p i hn
  · exact cut_head (Z := Z) (U := U) (r := r) (he := he) (S!) hx p i hy
      (fun j => cut_ghost (Z := Z) (U := U) (V := V) (hq := hq) (a := a) (he := he) Hp T' L (p j) i (hF j) (hn j)) hg
  · exact fun v hw hs => Streaks (Z := Z) (U := U) (V := V) (a := a) (hq := hq) Hp T' v he hw hs i
end YM.OPE.Stroke
