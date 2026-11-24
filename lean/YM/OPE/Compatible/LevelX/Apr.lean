import YM.OPE.Compatible.LevelX.Roth
/-!
# Ball top mean eta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
open Hark
-- preL journey for G all phases.D≤d
structure Stern (S:Sponsor G)(P:Patch)(τ:Phase→ℕ)(e d:ℕ)(U:ℝ):Prop where
      mark : e ≤d
      aware : Aware d τ
      oak : e+3 ≤ P.J
      tempo (D: Train P.J)(z:Phase)(x:bed G (d+z.val) (τ z)): ‖journey (ship P D) S.K P.order_cut (S.affordable P) x‖ ≤ U*‖x‖
      empty : 0 ≤ U
      toll (D: Train P.J)(z:Phase)(x:bed G (d+z.val) (τ z))(h:e <τ z)(hk:x∈fillet G (d+z.val) (τ z) (e+1) (by omega)): ‖journey (ship P D) S.K P.order_cut (S.affordable P) x‖ ≤ EndPrice e P.L*‖x‖
lemma rally (S:Sponsor G)(j:ℕ)(he:e≤d)(hp:e+3≤j)(hz:4 ≤ j)(hT:Aware d τ): ∃ v:ℝ,∃ n:ℕ,∀ L:Side, n ≤ L.val →∀ (ha:3≤L.val)(hb:Odd L.val),Stern S (⟨L,j,hz,ha,hb⟩:Patch) τ e d v:=by
      choose a ha H using fun i:Phase=> rides (j:=j) (i:=j) G S.K 0 (by omega) hz hz (d+i.val) (τ i) (by omega); choose b hb B using fun i:Phase=> rides (j:=j) (i:=j) G S.K (e+1) (by omega) hz hz (d+i.val) (τ i) (by have hh:=hT.credit i;omega); let z:=∑ i,b i; let x:= ∑ i,a i; have hx(i):a i≤ x:= single_le_sum (f:=a) (fun i _=> ha i) (mem_univ _); obtain ⟨r,hr⟩:= exists_nat_gt (4*z); refine ⟨x,r,fun L hL hℓ hZ=>⟨he,hT,hp,?_,(ha 0).trans (hx 0),?_⟩⟩
      · intro v n x; let P:Patch:=⟨L,j,hz,hℓ,hZ⟩; apply (H n (ship P v) x (dawn x) (S.affordable P)).trans; rw [pow_zero,mul_one]; exact mul_le_mul_of_nonneg_right (hx n) (norm_nonneg _)
      intro v n x hg hs; let P:Patch:=⟨L,j,hz,hℓ,hZ⟩; apply (B n (ship P v) x hs (S.affordable P)).trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); change b n*(L.val:ℝ)⁻¹^(e+1) ≤ (L.val:ℝ)⁻¹^e/4; have hq: b n ≤z := single_le_sum (f:=b) (fun i _=>hb i) (mem_univ _); have hh:b n* (L.val:ℝ)⁻¹ ≤ 1/4:=by
           rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : (0:ℝ)< L.val)]; have hv:r ≤ (L.val:ℝ):= by exact_mod_cast hL
           linarith
      rw [pow_succ',← mul_assoc]; apply (mul_le_mul_of_nonneg_right hh (by positivity :0≤ (L.val:ℝ)⁻¹^e)).trans_eq; ring
variable (ht:Stern K P τ e d v)
include ht
lemma sternCap (u:Phase): e<τ u:=by have h:=ht.aware.credit u; have hp:=ht.mark; omega
abbrev Turns (u:Phase):= tuneG G e (d+u.val) (τ u) (sternCap ht u) (ht.mark.trans (Nat.le_add_right ..)) v P.L P.coarse
private lemma statute_edgewise (B : Medal P G K.K P.J) (h : LocalRatio R) (hs : G.Simple)
    (S : Sailing T P p R b) (i : ℕ) : Edgewise (culm B h hs S ht.aware i) := by
  intro k z hk j hj
  by_cases he : k < 3
  · exact (collarH B h hs S ht.aware z i ⟨k, he⟩ (fun j hJ => hk _ hJ)).1 j hj
  rw [(show trims k z from hk).drop (show 3 ≤ k by omega) |>.limb, map_zero]
  rfl

private lemma statute_stride (B : Medal P G K.K P.J) (h : LocalRatio R) (hs : G.Simple)
    (S : Sailing T P p R b) (i : ℕ) (j : Phase) (a : bed G (d+j.val) (τ j)) :
    stride (culm B h hs S ht.aware i) j a =
      journey (ship P (S.U i).gear) K.K P.order_cut (K.affordable P) a := by
  let y : Tracts G d τ := Pi.single j a
  have hy : y j = a := Pi.single_eq_same ..
  change (culm B h hs S ht.aware i y) j = _
  apply Subtype.ext
  have hz : rare j y := fun i hi => Pi.single_eq_of_ne (ne_of_lt hi) _
  have hx := (collarH B h hs S ht.aware y i j hz).2
  rw [hy] at hx
  exact hx

private lemma statute_flag (j : Phase) {q : ℕ} (hq : q ≤ e+1) :
    (Turns ht j).flag q = fillet G (d+j.val) (τ j) q (by have := sternCap ht j; omega) := by
  simp only [Turns, tuneG, min_eq_left hq]

private lemma statute_tap (j : Phase) {q : ℕ} (hq : q < e+1) :
    (Turns ht j).Tap q = stepRead G e q (d+j.val) (τ j) (by have := sternCap ht j; omega) :=
  dif_pos hq

private lemma statute_grooved (D : Train P.J) (j : Phase)
    (f : bed G (d+j.val) (τ j) →L[ℝ] bed G (d+j.val) (τ j))
    (hf : ∀ a, f a = journey (ship P D) K.K P.order_cut (K.affordable P) a) :
    Grooved (Turns ht j) f := by
  have ho := ht.oak
  have hc := sternCap ht j
  constructor
  · intro q he x hx
    rw [statute_flag ht j he] at hx ⊢
    rw [hf]
    exact survivor (ship P D) K.K P.order_cut (K.affordable P) x (by omega) (by omega) hx
  · intro q he x hx
    rw [statute_flag ht j he.le] at hx
    rw [statute_tap ht j he, hf]
    exact priceS (ship P D) K.K P.order_cut (K.affordable P) x (e := q) (d := e)
      (show q ≤ P.J-1 by omega) (show q < τ j by omega) hx (show q ≤ e by omega)
  · intro x hx
    rw [statute_flag ht j le_rfl] at hx
    rw [hf]
    exact ht.toll D j x hc hx
  · apply ContinuousLinearMap.opNorm_le_bound _ ht.empty
    intro x
    rw [hf]
    exact ht.tempo D j x

set_option maxHeartbeats 200000 in
lemma statute (B:Medal P G K.K P.J)(h:LocalRatio R)(hs:G.Simple)(S:Sailing T P p R b)(i:ℕ): Assist (Turns ht) (culm B h hs S ht.aware i):=by
  exact ⟨statute_edgewise ht B h hs S i, fun j =>
    statute_grooved ht (S.U i).gear j _ (statute_stride ht B h hs S i j)⟩
end YM.OPE.Drift
