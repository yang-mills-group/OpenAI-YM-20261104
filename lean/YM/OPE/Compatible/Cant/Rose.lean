import YM.OPE.Compatible.Cant.Orb
/-!
# Vanishing pairings after transport of a zero readout

At a grade satisfying `Carries`, `YM.OPE.Stroke.portraitK` transfers a zero source readout to vanishing of both pairings of its corresponding target readout with any test vector.
The conclusion holds at every order and phase for pinned sites on sufficiently large even lattices.
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
local notation "Cρ"=> Carries (hp:=hp) (ht:=ht) (hq:=hq) (V:=V) (A:=A) (hz:=hz) Z a f' U U' i' j'
private lemma pairWithZeroReadout (e : J!) (n : Side) (t : Even n.val) (x y : Site n)
    (hv : barrier P ≤ n.val) (hh : Pins K P x y) (ph : Phase) (k : ℕ)
    {v : Mint Z e.val} (hv0 : v = 0) (b : Mint Z e.val) :
    Por Hp Z e.val ph t x y a k v b = 0 ∧ Por Hp Z e.val ph t x y a k b v = 0 := by
  subst v
  have hz : (0 : Mint Z e.val) ∈ Dross Hp Z a e.val := (Dross Hp Z a e.val).zero_mem
  have values := hz n t x y hv hh k ph b
  exact ⟨(flareP Hp Z a 0 b t x y ph k).trans values.1,
    (flareP Hp Z a b 0 t x y ph k).trans values.2⟩

include hX he h' hv L T₀
set_option maxHeartbeats 200000 in
lemma portraitK {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ)(e:J!) (h:Cρ e.val) (v:F!)(q: U.flag e.val i')(p: U'.flag e.val j') (hy:v-q.val∈ Sγ i')(hx:f' v-p.val∈ CΓ)(hp':U.read e.val e.isLt i' q=0) (b:Mint Z e.val):∀ (n:Side)(t:Even n.val)(x y:Site n)(_hx:barrier P≤n.val)(_hq:Pins K P x y)(l':Phase)(k':ℕ), Por Hp Z e.val l' t x y a k' (U'.read e.val e.isLt j' p) b=0 ∧ Por Hp Z e.val l' t x y a k' b (U'.read e.val e.isLt j' p)=0:=by
        intro n t x y hv' hh l' m'; have hb: Vγ e b:= jewelN (juneX (hq:=hq) (hz:=hz) Hp Z a hX he f' i' j' h' hv L T₀ C e h) b; obtain ⟨u,z,hU,rfl⟩:=hb
        have hz':u.val-u.val∈ Sγ i':=by rw [sub_self];exact (Sγ i').zero_mem
        have ht' := pairWithZeroReadout Hp Z a e n t x y hv' hh l' (m'+r) hp'
          (U.read e.val e.isLt i' u)
        have hA:= commuting (hq:=hq) (hz:=hz) Hp Z a hX t x y hh he f' i' j' e hv' l' T₀ v u.val q u p z hy hz' hx hU m'; have hD:=commuting (hq:=hq) (hz:=hz) Hp Z a hX t x y hh he f' i' j' e hv' l' T₀ u.val v u q z p hz' hy hU hx m'; exact ⟨hA.symm.trans ht'.1,hD.symm.trans ht'.2⟩
end
end YM.OPE.Stroke
