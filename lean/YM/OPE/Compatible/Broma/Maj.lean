import YM.OPE.Compatible.Broma.Wax
/-! # actual op stability staging. norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
-- automatic Era.Vary.C
lemma bona (B:Medal P G K.K P.J)(x y:Alps K T P.J v)(z:ℝ)(hp:Charm P.L x y z R):Era (charmSeal B x.gear) x:=by
     let A:=ship P x.gear; have ht:= interlock P _ _ hp; obtain ⟨h,hv⟩:=hp; have hx : A.patch=P:= by cases P; rfl
     convert! sprig (A:=x) (D':=y) A (show Medal A.patch G K.K P.J from hx.symm ▸ B) h (by rfl) ht using 1
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
variable (B:Medal P G K.K P.J)(H:LocalRatio R)(hs:G.Simple)(hp:Crest G P K.K m)(ha:Aware d τ)
local notation "UX" => (Qmark B (UA (H:=T) (P:=P) (p:=p) (V:=R) (C:=b)))
local notation "YX" => (Qmark B (VA (H:=T) (P:=P) (p:=p) (V:=R) (C:=b)))
lemma deckB (V:Sailing T P p R b)(i:ℕ): Era (charmSeal B (V.U i).gear) (V.U i):= bona B (V.U i) (V.U (i+1)) _ (V.shot i)
noncomputable def YangZ (B:Medal P G K.K P.J)(H:LocalRatio R)(hs:G.Simple)(V:Sailing T P p R b)(hp:Aware d τ)(s:ℝ) (i:ℕ): Tower (Shade G) d τ →L[ℝ] Tower (Shade G) d τ:= actor (V.U i) (charmSeal B (V.U i).gear) R s ⟨hs,H,deckB B V i⟩ hp
include hp
lemma affordZ (s:ℝ)(he:∀ i,τ i≤m):
     Brim (fun i:X! => YangZ B H hs i.1.1 ha s i.2) (fun i:X! => YangZ B H hs i.1.2 ha s i.2) u! q! :=by
          have hv: 1≤u!:=max_cap (P:=P) (H:=T) (p:=p) (V:=R) (C:=b); have hq:0≤q!:=fun i=>by unfold downK; positivity
          apply Wπ hv hq; intro i
          let U(k: X!) := Qmark B UA k;let V(k:X!):=Qmark B VA k
          let L(k:X!):RollD (UA k) (U k) R:=⟨hs,H,deckB B k.1.1 k.2⟩;let X(k:X!):RollD (VA k) (V k) R:=⟨hs,H,deckB B k.1.2 k.2⟩
          let f(j:Phase): Tower (Shade G) d τ→L[ℝ] _:= ContinuousLinearMap.proj j
          let K1(y:Phase) (k:X!):= Drift.chamber (UA k) (U k) R s y i (L k) ha
          let K2(y:Phase) (k:X!):= Drift.chamber (VA k) (V k) R s y i (X k) ha
          have ht(j:Phase): Brim (K1 j) (K2 j) u! q! :=by
               by_cases he':j ≤ i; swap; · unfold K1 K2 Drift.chamber; simp_rw [dif_neg he']; exact Brim.constant _
               have hP:= civic B H hp hs j i s d (τ j) (he _) (awareLeaf ha j) (fun i:X! => (L i).eph) (fun i:X! => (X i).eph)
               unfold K1 K2 Drift.chamber; simp_rw [dif_pos he']; exact Canal hP (Brim.constant _) hv hq
          have hx(j:Phase): Brim (fun k:X! => K1 j k ∘L f j) (fun k:X! => K2 j k ∘L f j) u! q!:= Canal (Brim.constant _) (ht j) hv hq
          convert! Brim.way _ _ Finset.univ (fun j _=> hx j) hv hq using 1
