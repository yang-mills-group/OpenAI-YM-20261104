import YM.FVA2.Hearth.Term
/-!
 # Full predictor choices (shared across products)

 A finite Witness clan across the one hierarchy. Decorates each layer with ONE branch
 on ALL clusters. Within a truss (also including changes of truss after adjusting each
 brand of clock) even these different fixed choices give the SAME series of the whole
 `drive` and not merely the same integrated terminal result. This is an equality of
 formal valuation after unmasking, not asserting these choices evaluate equal globally
 when leaving small-field sector.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {c f n:Side} {L:Fabric G n}

def Clan {n: Side}(L: Fabric G n) : Type:= match L with
 | .endcap _ _=> Unit
 | .layer S _ _ _ L=> S.Choices × Clan L
@[implicit_reducible] def iClan {n:Side}(L: Fabric G n): Fintype (Clan L) := by
 cases L with
 | endcap=> unfold Clan; infer_instance
 | layer _ _ _ _ L=> letI:= iClan L; unfold Clan; infer_instance
termination_by structural L
attribute [instance] iClan

def changeTag {n:Side}(L:Fabric G n)(u:Clan L) : Fabric G n:= match L with
 | .endcap k h => Fabric.endcap k h
 | .layer S H _ hf L=> Fabric.layer S H (show S.Choices × Clan L from u).1 hf (changeTag L (show S.Choices×Clan L from u).2)
variable (L) (t:Clan L)
namespace Clan
def install {n:Side}(L: Fabric G n)(T:Cloth L)(u:Clan L): Cloth (changeTag L u) := by
 cases T with
 | floor k h F=> exact Cloth.floor n h F
 | @inLayer c f S b t hf L P C=>
     exact Cloth.inLayer P (install L C (show S.Choices×Clan L from u).2)
termination_by structural T
lemma lowest {n:Side}(L: Fabric G n)(u:Clan L): Facade.Bottom (changeTag L u)=Facade.Bottom L:= by
 cases L with
 | endcap=> rfl
 | layer S H _ _ L=> exact lowest L (show S.Choices×Clan L from u).2
termination_by structural L

-- inverse direction keeps reference.L table entries universal
def accounts {n:Side}(L: Fabric G n)(u:Clan L) : (changeTag L u).Cost ≃ L.Cost:= match L with
 | .endcap _ _=> Equiv.refl _
 | .layer S _ _ _ L=> Equiv.optionCongr (accounts L (show S.Choices×Clan L from u).2)
-- OTP next canonical payroll
section
abbrev Stuck (G: Gauge)(n:Side):= Unmasked G n × Ticket (Flats G n)
def report {m n:Side}(k:m=n)(p:Stuck G m): Stuck G n:= k ▸ p

variable {J:ChartRatio G}
-- Reader for any core profile through cutoff. holds clock external numerical choices fixed at each step. La.
theorem echoed {n:Side}(L:Fabric G n)(T:Cloth L)(t:Clan L)(r:ℕ)(z w:L.Cost→PowerSeries ℝ)(hW:∀ i,Through r (z i) (w i)){U V: Unmasked G n} (g_Z:Commission J T V w) (g_W: Commission J (install L T t) U (z ∘ (accounts L t))) {A B:Ticket (Flats G n)}(H:Profile r (U,A) (V,B))(hU:incline U.W)(hV: incline V.W)(hj:LocalRatio J): Profile r (report (lowest L t) (drive (install L T t) (z ∘ accounts L t) U A J g_W)) (drive T w V B J g_Z):= by
 cases T with
 | floor=>
    rw [drive]; exact H -- reduce?
 | @inLayer c f S h u hf L P C=>
    change S.Choices × Clan L at t; let v:= t.2; let b:= install L C v; let g:= accounts L v; let k:(changeTag L v).Cost→PowerSeries ℝ:= (z ∘ some) ∘ (g);
    unfold report; rw [drive];
    let x := Exists.choose g_W
    let y := Exists.choose g_Z
    let U' := Update P t.1 J (z none) U x
    let V' := Update P u J (w none) V y
    let M:= Broadcast P t.1 J (z none) U x (boost (blankRight P) A)
    let N:= Broadcast P u J (w none) V y (boost (blankRight P) B)
    have he:Profile r (U',M) (V',N):= ⟨holdPrice h t.1 u P H.Q (hW none) x y J,syncWeight h t.1 u P H.Q (hW none) x y J H.W,syncPay h t.1 u P H.Q (hW none) x y hU hV H.W hj H.F⟩
    let hv := Exists.choose_spec g_W; let hw:=Exists.choose_spec g_Z
    change Profile r (report _ (drive b k U' M J hv)) _
    exact echoed L C v r (z∘some) (w∘some) (fun i=> hW (some i)) hw hv he (funded hj (z none) hU x) (funded hj (w none) hV y) hj
termination_by structural T

lemma actual_collect (p v:Stuck G n) (h:∀ r,Profile r p v): p=v:= by
 rcases p with ⟨⟨a,b⟩,c⟩; rcases v with ⟨⟨a',b'⟩,c'⟩;
 obtain rfl:a=a':= (h 0).Q; obtain rfl:b=b':=PowerSeries.ext fun i=> (h i).W i le_rfl; obtain rfl:c=c':= PowerSeries.ext fun i=> (h i).F i le_rfl; rfl
variable (z:L.Accounts→ PowerSeries ℝ)
-- keep top & each level account the SAME statement of trajectory, independent of tags
def quote (c:(changeTag L t).Accounts): PowerSeries ℝ:= z (Option.map (accounts L t) c)
lemma quote_top : Clan.quote L t z none=z none:= rfl
lemma quote_later (c): Clan.quote L t z (some c)=z (some ((accounts L t) c)):= rfl
variable (T:Cloth L) (hj:LocalRatio J) (H:∀ i,0<term (z i) 0)
include H
lemma found (i): 0<term (Clan.quote L t z i) 0:= H _
local notation "p"=> Clan.quote L t z
local notation "Q"=> Facade.drive T (z ∘ some) (headquarters z)
local notation "q"=> collared T z hj H
variable (v: Ticket (Flats G n)) (O: Wilson.Config G n→ℝ)
theorem all_values : report (lowest L t) (drive (install L T t) (Clan.quote L t z ∘ some) (headquarters (Clan.quote L t z)) v J (collared (install L T t) p hj (found L t z H))) = Q v J q:= actual_collect _ _ fun r=> echoed L T t r (z∘some) (z∘some) (fun _=> Through.refl _) q (collared _ p hj (found L t z H)) ⟨rfl,Through.refl _,Through.refl _⟩ (OpenSlots.restores ..) (OpenSlots.restores ..) hj

lemma works (R:Cloth (changeTag L t))(hO:PreTest O){Y:ChartRatio G}(yh:LocalRatio Y): report (lowest L t) (drive R (Clan.quote L t z ∘ some) (headquarters p) (imprintRoot O) Y (collared R p yh (found L t z H)))= Q (imprintRoot O) J q := by
 rw [← all_values L t z T hj H (imprintRoot O)]; apply congr_arg; exact Prod.ext (any_state R (install L T t) p (found L t z H) yh hj _ _) (any_tree R (install L T t) O hO p (found L t z H) yh hj)
-- can average / take mixtures only with correct common normalization; no branch cost assertion

end
end Clan
end YM.FVA2.Hearth
