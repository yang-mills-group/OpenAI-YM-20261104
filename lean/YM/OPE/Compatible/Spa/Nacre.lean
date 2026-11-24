import YM.OPE.Compatible.Spa.Coin
/-!
# Vanishing on the next flag and on `Sapling`

`cuspTop'` shows that `Gift` preserves the next flag under the `Floss` hypotheses.
With the `Bals` data, `deepRun` proves that `ReadK` vanishes on flag elements in
the sum of that deeper flag and `Sapling`. The proof applies linearity to the
two vanishing statements separately.
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
local notation "JΛ"=> Fin (l+1) 
open Pipes
lemma cuspTop' (U:Z.Ω M Y)(T':Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(e:J!)(x:M)(p:F!)(hx:p∈ U.flag (e.val+1) x): Gift G D₀.aware p∈ U.flag (e.val+1) x:=by
      let y:U.flag e.val x:=⟨p,U.moves _ _ e.isLt hx⟩; obtain ⟨q,h,H⟩:=T'.turn e.val e.isLt x y; have hp:= (U.depth e.val x e.isLt y).1 hx; have ht:= (U.depth e.val x e.isLt q).2 (by rw[H,hp,map_zero]); exact h ▸ ht
-- Vanishing on the sum of the two submodules.
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
private lemma readSupZero {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (S A B : Submodule ℝ E) (le : A ≤ S)
    (L : S →ₗ[ℝ] F) (ha : ∀ x : S, x.val ∈ A → L x = 0)
    (hb : ∀ x : S, x.val ∈ B → L x = 0) (x : S) (hx : x.val ∈ A ⊔ B) :
    L x = 0 := by
  obtain ⟨v, hv, w, hw, add⟩ := Submodule.mem_sup.mp hx
  let v' : S := ⟨v, le hv⟩
  have diff : (x - v').val = w := by
    change x.val - v = w
    rw [← add]
    abel
  have inB : (x - v').val ∈ B := by rw [diff]; exact hw
  have zero := hb (x - v') inB
  rw [map_sub, ha v' hv, sub_zero] at zero
  exact zero

private lemma deeperReading {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (U : Z.Ω M Y) (e : J!) (x : M) (v : U.flag e.val x) (hv : v.val ∈ U.flag (e.val + 1) x) :
    ReadK Z κ U e x v = 0 :=
  (congrArg (κ e) ((U.depth e.val x e.isLt v).1 hv)).trans (map_zero (κ e))

private lemma nullReading {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (U : Z.Ω M Y)
    (T' : Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
    (e : J!) (x : M) (v : U.flag e.val x) (hv : v.val ∈ Sγ x) :
    ReadK Z κ U e x v = 0 :=
  ((C.tricks e).hero _).1 (stockMe Hp T' x v hv (he := e.isLt))

lemma deepRun {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ) (U:Z.Ω M Y)(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(e:J!)(x:M)(u:U.flag e.val x)(h:u.val ∈ Bay U.flag (Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)) (e.val+1) x):ReadK Z κ U e x u=0 := by
  exact readSupZero (U.flag e.val x) (U.flag (e.val + 1) x) (Sγ x)
    (U.moves _ _ e.isLt) (ReadK Z κ U e x) (deeperReading Z (κ := κ) U e x)
    (nullReading Hp Z a C U T' e x) u h

end YM.OPE.Stroke
