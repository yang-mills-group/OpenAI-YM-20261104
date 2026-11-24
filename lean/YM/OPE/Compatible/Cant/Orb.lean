import YM.OPE.Compatible.Cant.Villa
import YM.OPE.Compatible.Cant.Lip
/-!
# Realizing the first component of a transported readout

`YM.OPE.Stroke.Carries` requires the transport to map the sum of the source flag and its residual submodule into the corresponding sum at the target.
At a grade satisfying this condition, `juneX` proves that readouts represented by matching flags are closed under addition and the phase shift and realize every first component.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
variable {uα:I→ℝ}{A:(v:I)→Alps K T j (uα v)}
local notation "μ"=>lapPrice (Patch.L P)
section
variable (hX: Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
variable {ht:4 ≤ j}{hz:1≤uα}{U':Z.Ω I uα}
variable (he: Z.Floss A U' ht (le_trans zero_le_one hz) k Hp a)(f':Tracts G d τ→L[ℝ] Tracts G d τ) (i':M)(j':I)
local notation "AC"=> Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f'
local notation "CΓ"=>Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j'
variable (h':∀ i,(A i).clip=p')(hv:l*l≤ τ 0)(L:Lance X)(T₀: Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f')
local notation "Vγ" e:max v:max => InVivid (U:=U) (U':=U') (hz:=hz) (A:=A) (ht:=ht) Z a f' i' j' e v
abbrev Carries (N:Tracts G d τ→L[ℝ] Tracts G d τ)(U:Z.Ω M Y)(U':Z.Ω I uα)(x:M)(y:I)(e:ℕ):Prop:=∀ p:F!,p∈Bay U.flag Sγ e x→ N p∈ Bay U'.flag (Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀)) e y
local notation "Cρ"=> Carries (hp:=hp) (ht:=ht) (hq:=hq) (V:=V) (A:=A) (hz:=hz) Z a f' U U' i' j'
include he h' hv L T₀ in
private lemma phasePartner {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (e : J!) (hx : Cρ e.val) (w : U.flag e.val i') :
    ∃ q : U'.flag e.val j', f' w.val - q.val ∈ CΓ ∧ q.val 0 = f' w.val 0 := by
  have hQ := hx w.val (le_sup_left (a := U.flag e.val i') w.property)
  have flag := (T₀.flag e.val e.isLt.le w.val 0 (trims.be _)).2
    ((U.quake e.val e.isLt i' w 0 (trims.be _)).1)
  exact Earth (hq := hz) Hp Z a U' h' he C hv L e.val e.isLt.le j' (f' w.val) hQ flag

include he h' hv L T₀ in
private lemma reachFirstPhase {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (e : J!) (hx : Cρ e.val) (v : Bead G l e.val) :
    ∃ p : Mint Z e.val, Vγ e p ∧ UΦ Z e.isLt p 0 = v := by
  obtain ⟨w, hw⟩ := pumpZ Z i' U ((μ e.val^r)⁻¹ • v) e.isLt
  obtain ⟨q, hq', hfirst⟩ := phasePartner (Hp := Hp) (Z := Z) (a := a) (i' := i') (j' := j') (f' := f') (hq := hq) (hz := hz)
    (L := L) (he := he) (h' := h') (hv := hv) (T₀ := T₀) C e hx w
  have hscale := pupil (hp := hp) (ht := ht) (hq := hq) (hz := hz) (U := U) (U' := U')
    Z a f' i' j' T₀ e w q hfirst
  refine ⟨U'.read e.val e.isLt j' q, ⟨w, q, hq', rfl⟩, hscale.trans ?_⟩
  exact (congrArg ((μ e.val^r) • ·) hw).trans
    (smul_inv_smul₀ (pow_pos (EndFare ..) _ |>.ne') _)

include hX he h' hv L T₀
set_option maxHeartbeats 200000 in
lemma juneX {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ)(e:J!)(hx:Cρ e.val) : June (E:= ↥(Fruition Z.station (lapPrice P.L e.val))) (F:=Bead G l e.val) (BoxesΦ Z e.val e.isLt) (WaneZ Z e.val e.isLt).toLinearMap (fun x=>Vγ e x):=by
  refine ⟨tokensPlus (Z:=Z) (A:=A) (ht:=ht) (hz:=hz) (U:=U) (U':=U')
    a f' i' j' e, fun x h => tokensGrow (V:=V) (hq:=hq) (hz:=hz) Hp Z a hX he f' i' j' _ _ h T₀,
    (ideaΓ Z e.isLt).inverse', ?_⟩
  exact reachFirstPhase (Hp := Hp) (Z := Z) (a := a) (i' := i') (j' := j') (f' := f') (hq := hq) (hz := hz) (L := L) (he := he) (h' := h') (hv := hv)
    (T₀ := T₀) C e hx
end
end YM.OPE.Stroke
