import YM.OPE.Compatible.Karu.Rule
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
variable (Y Z:(solar G d τ)→L[ℝ] (solar G d τ))(hp:LocalRatio R)(hq:Aware d τ)(he:Crest G P K.K m)(hs:G.Simple)
variable (B: Medal P G K.K P.J)
variable (F:Sailing T P p R b)(H:Even c.val)
abbrev CountL (n L:Side):ℕ→ Side
   | 0=> n
   | j+1=> CountL n L j* L
variable {N:Side}
abbrev trip (K:Sponsor G)(P:Patch)(i:ℕ)(n:Side):Ratio (CountL n P.L i) (CountL n P.L (i+1)):= χ' _ P K
lemma hosts (c L:Side)(i:ℕ):((CountL c L i).val:ℝ)= c.val*(L.val:ℝ)^i := by induction i with
   | zero=> rw [pow_zero,mul_one]
   | succ i ih=> rw [show (CountL ..).val= _ from (show (CountL c L (i+1)).val= _ from (show _=_ from (show (CountL c L (i+1)).val=(CountL c L i).val*L.val from rfl))), Nat.cast_mul,ih,pow_succ]; ring
lemma stalk (c L:Side)(i:ℕ): c.val≤ (CountL c L i).val:=by
   have h:c.val ≤ ((CountL c L i).val:ℝ):=by rw [hosts]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (W_le _))
   exact_mod_cast h
abbrev spikeS (K:Sponsor G)(P:Patch)(u:Site c): (i:ℕ)→Site (CountL c P.L i)
   | 0=>u
   | k+1=> (trip K P k c).embed (spikeS K P u k)
def Pins (K:Sponsor G)(P:Patch)(x y:Site c) :Prop:= ∃ v:ℝ,2 ≤ v ∧∀ i, Settle (spikeS K P x i) (spikeS K P y i) v
lemma evenBoot (K:Sponsor G)(P:Patch)(H:Even c.val)(i:ℕ): Even (CountL c P.L i).val:=by induction i with
   | zero=>exact H
   | succ i ih=> exact even_both (trip K P i c) ih
noncomputable abbrev Fitt (x y:Site c)(ψ:Phase) (i j:ℕ): Dice (Tracts G d τ):= FstV Y Z hp hq hs F i (CountL c P.L j) (evenBoot K P H j) (spikeS K P x j) (spikeS K P y j) ψ
local notation "θ"=> θC
local notation "L!"=> Sailing T P p R b
abbrev ΓX (d:ℕ):= max (Rune d) (Dosage d)
abbrev χV (P: Patch)(d:ℕ):= (P.L.val:ℝ)^ΓX d
include H he
-- loans Π and variations
lemma tides (W:Type)(q:W→ TileC T P p R b)(h:∀ i,upperX (q i) ≤ v)(x y:Site c)(ψ:Phase)(s:W→ℕ): ∃ b:ℝ,0 ≤ b∧∀ i:W, let p:=q i
     let f:= Fitt Y Z hp hq hs p.1.1 H x y ψ p.2 (s i); let g:= Fitt Y Z hp hq hs p.1.2 H x y ψ p.2 (s i); ‖f‖≤ b*(χV P d)^(s i) ∧ ‖f-g‖≤ b*(χV P d)^(s i)*θC^p.2:=by -- ω
      let n(i:W):=CountL c P.L (s i); let t(i):=spikeS K P x (s i); let u(i):= spikeS K P y (s i); let h':= Goss (n:=n) Y Z hp hq he hs q v h (fun i=>evenBoot K P H (s i)) t u ψ; let p(i:W):= Fitt Y Z hp hq hs (q i).1.1 H x y ψ (q i).2 (s i); let g:= ΓX d; have hv(i:W):((n i).val:ℝ)^g = (c.val:ℝ)^g*(χV P d)^(s i):=by unfold n; rw [hosts,mul_pow,← pow_mul]; unfold χV; rw [show s i*g=g*s i from mul_comm ..,pow_mul]
      have he':Cash n (ΓX d) 1 (fun i=> ‖p i‖):= costGauge n h'.1 zero_le_one le_rfl (le_max_left ..)
      obtain ⟨a,ha,hx⟩:= bundleP.mp (show NPay n p (ΓX d) 1 from he'); obtain ⟨b,hb,hY⟩:= bundleP.mp h'.2; let V:=(c.val:ℝ)^g; have hV:0 ≤ V:=by unfold V; positivity
      let D:= (a+b)*V; refine ⟨D,(by unfold D;positivity),fun i=>?_⟩; dsimp only; have hp:0 ≤ ((χV P d)^(s i)):=(by unfold χV; positivity); constructor
      · have h:= hx i; rw [Pi.one_apply,mul_one,hv] at h; apply h.trans; unfold D V; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb) hV) hp
      apply le_trans (hY i); rw [show ((n i).val:ℝ)^_ =_ from hv i, ← mul_assoc b,Function.comp_apply]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) hV) hp) (fixedTheta _)
end YM.OPE.Quit.PriceZ
