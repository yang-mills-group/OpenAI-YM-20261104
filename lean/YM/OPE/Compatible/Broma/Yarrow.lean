import YM.OPE.Compatible.Broma.Sov
/-!
# Snapshot through finite seams degree.Lpere
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
section Norms
variable [NormedAddCommGroup E][NormedSpace ℝ E] {X W:M→ℝ}
variable {p q:M→ E}
lemma brimScale (u:ℝ)(hp:Brim p q X W): Brim (u • p) (u • q) X W:=by
     have he {p:M→E}{v:M→ℝ}(h:Wealth p X v): Wealth (u • p) X v:=by obtain ⟨c,b,n,H⟩:=h; refine ⟨‖u‖*c,mul_nonneg (norm_nonneg _) b,n,fun i=>?_⟩; rw [Pi.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left (H i) (norm_nonneg _)).trans_eq (by ring)
     refine ⟨he hp.A,he hp.B,?_⟩; rw [← smul_sub]; exact he hp.D
noncomputable def cexpR (f:E→L[ℝ] E)(t:ℝ)(n:ℕ):E→L[ℝ] E:=∑ i∈range (n+1),(t^i/(i.factorial:ℝ)) • f^i
lemma expAt (A:E→L[ℝ] E)(t:ℝ)(n:ℕ) (x:E): cexpR A t n x=fixExp A.toLinearMap t n x:=by
      unfold cexpR; rw [_root_.sum_apply,Hflow]; apply sum_congr rfl; intro i hi; rw [_root_.smul_apply]; apply congr_arg; suffices h: ∀ i:ℕ,(A^i) x=(A.toLinearMap^i) x from h i; intro i; induction i with
      | zero=>rfl
      | succ i ih=> rw [pow_succ', pow_succ']; change A ((A^i) x)= A _; rw [ih]
lemma brimExp {p q:M→ E→L[ℝ] E}(hp:Brim p q X W)(t:ℝ)(n:ℕ)(hx:1≤ X)(hw:0≤W): Brim (fun i=> cexpR (p i) t n) (fun i=> cexpR (q i) t n) X W:=by
     have h(i:ℕ):Brim (fun j=> p j^i) (fun j=>q j^i) X W:=by induction i with | zero=> simp_rw [pow_zero]; exact Brim.constant (1:E→L[ℝ] E)| succ i ih=> simp_rw [pow_succ']; exact Canal ih hp hx hw
     exact Brim.way _ _ (range (n+1)) (fun i _=>brimScale (t^i/(i.factorial:ℝ)) (h i)) hx hw
omit [NormedSpace ℝ E] in
lemma Brim.up (hp:Brim p q X W){Y:M→ℝ}(hh:1 ≤ X)(h: W ≤ Y): Brim p q X Y:=by refine ⟨hp.A,hp.B,?_⟩; obtain ⟨a,H,k,he⟩:=hp.D; exact ⟨a,H,k,fun i=>le_trans (he i) (mul_le_mul_of_nonneg_left (h i) (mul_nonneg H (pow_nonneg (zero_le_one.trans (hh _)) k)))⟩
end Norms
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
-- real inverse small phases
noncomputable abbrev puffX (G:Gauge)(m k:ℕ)(C:KernelChoices)(v:Train r)(h:4 ≤ r)(u:ℝ): Seat k m (Shade G)→L[ℝ] Seat k m (Shade G):= cexpR (lapD (atlasF G v h C) m k) u k
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
noncomputable abbrev θC :ℝ:=Real.sqrt (1/2:ℝ)
lemma thetaC :0<θC ∧ θC < 1:=by
                                        constructor; swap;· unfold θC; rw [Real.sqrt_lt' (by positivity)]; norm_num
                                        exact Real.sqrt_pos.2 (by norm_num)
abbrev fareI (v:M×ℕ):ℝ:= θC^v.2
lemma fixedTheta (i:M×ℕ):0≤ fareI i:= pow_nonneg thetaC.1.le _
lemma thetaL (i:M×ℕ):downK i ≤ fareI i:=by apply pow_le_pow_left₀ (by norm_num); have ht:=Real.sq_sqrt (by norm_num : 0≤ (1/2:ℝ)); change (1/2:ℝ)≤θC; change θC^2= _ at ht; nlinarith only [thetaC.1,thetaC.2,ht]
lemma brimPuff (s:ℝ) (hp:Crest G P K.K m) (k r:ℕ): Brim (fun i:X! =>puffX G k r K.K (UA i).gear P.order_cut s) (fun i:X! =>puffX G k r K.K (VA i).gear P.order_cut s) u! fareI:=by
     obtain ⟨B⟩:= medal_buy P.odd_side (K.affordable P) P.order_cut; obtain ⟨σ,F,h,H,a,c,n,hA⟩:= running T P B p R b hp; have hh:= H.fuel
     refine brimExp ?_ s r hh (fun i=>fixedTheta i)
     let E(Z:Train P.J):=lapD (atlasF G Z P.order_cut K.K) k r; let D:= Silt.wind r; have ht:0 ≤ D:=by unfold D Silt.wind; positivity
     have hL (p:X!→Train P.J): Wealth (fun i=> E (p i)) upperX 1 := by
          let v:= (terra_money K.K P.order_cut).choose; have hv:0≤v:= (terra_money K.K P.order_cut).choose_spec.1; refine ⟨D*v,mul_nonneg ht hv,0,fun i=>?_⟩;rw [Pi.one_apply,pow_zero,mul_one,mul_one]; exact lapE ..
     let W:= (told K.K P.order_cut).choose; have hW:0≤ W:= (told K.K P.order_cut).choose_spec.1
     refine ⟨hL _,hL _,D*(W*Real.sqrt a),mul_nonneg ht (mul_nonneg hW (by positivity)), n,fun i=>?_⟩; let V:= a*upperX i ^ n; let x:ℝ:= downK i; have hx:0 ≤ x:= (H.tune i).le; have hr: 1 ≤ upperX i^n:= one_le_pow₀ (hh i); have hv:0≤ V:=mul_nonneg c (zero_le_one.trans hr); let q:= (UA i).gear; let y:=(VA i).gear; change ‖E q-E y‖ ≤ _; apply le_trans (CotWarp q y _ K.K σ (V*x) h.le (mul_nonneg hv hx) (hA i) k r); change D*(W*Real.sqrt (V*x)) ≤ D*(W*Real.sqrt a)*_*_
     have he:Real.sqrt x = fareI i:= by rw [show x=(fareI i)^2 from (by unfold x fareI θC downK; rw [← pow_mul, mul_comm i.2, pow_mul,Real.sq_sqrt (by norm_num)]),Real.sqrt_sq (fixedTheta i)]
     rw [Real.sqrt_mul hv,he]; have hy: Real.sqrt V ≤ Real.sqrt a*upperX i ^n:=by
          unfold V; rw [Real.sqrt_mul c]; exact mul_le_mul_of_nonneg_left (by apply le_of_sq_le_sq _ (zero_le_one.trans hr); rw [Real.sq_sqrt (zero_le_one.trans hr),pow_two]; exact le_mul_of_one_le_right (zero_le_one.trans hr) hr) (by positivity)
     apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy (fixedTheta i)) hW) ht); exact le_of_eq (by ring)
end YM.OPE.Drift
