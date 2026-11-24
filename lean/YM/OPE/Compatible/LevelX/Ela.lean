import YM.OPE.Compatible.Grotto.Def
import YM.OPE.Compatible.LevelX.Apr
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
variable (h:G.Simple) (hp:Stern K P τ e d v) (p':Medal P G K.K P.J)(hw:LocalRatio R)
local notation "Y!" => Sailing T P p R b
abbrev Quoin (x:Y!):= culm p' hw h x hp.aware
local notation "A!"=> Tracts G d τ
local notation "L!"=> (Quoin (T:=T) (p:=p) (b:=b) h hp p' hw)
include p' h hp hw
lemma FlapZen (ht:Crest G P K.K m)(hx:∀ i,τ i ≤ m) [Nonempty (Y!)] : ∃ V:A!→L[ℝ] A!,Assist (Turns hp) V∧ Yeast (Y!) (L!) V Sailing.cost θC ∧∀ x:Y!, Tendsto (L! x) atTop (𝓝 V):=by
      have ha(j:Y!):1 ≤ j.cost:=j.fits; have he:= shines (m:=m) (T:=T) (p:=p) (b:=b) p' hw h ht hp.aware hx; have hX(x:Y!)(i j:ℕ): L! (x.shiftS i) j= L! x (i+j):=rfl
      obtain ⟨X,hY,hF⟩:= Roof (a:=Sailing.cost) ha L! Sailing.shiftS hX (fun _ _=>rfl) thetaC.1.le thetaC.2 he.D; let z:=Classical.arbitrary (Y!); refine ⟨X,closedAssist _ _ (hF z) (fun i=>statute hp p' hw h z i),⟨?_,hY⟩,hF⟩ -- completeSpace
      obtain ⟨B,Hb,k,H⟩:= he.A; let f(i:Y!):=B*i.cost^k; refine ⟨f,⟨B,Hb,k,fun i=>?_⟩,fun i j=>?_⟩
      · unfold f; have hh:0 ≤ i.cost:=zero_le_one.trans (ha i); rw [Real.norm_of_nonneg (mul_nonneg Hb (pow_nonneg hh _)),Pi.one_apply,mul_one]
      rw [one_pow,mul_one]; unfold f; have hp:=H ((i,i),j); change ‖_‖≤ B*max i.cost i.cost ^k*1 at hp; rw [max_self,mul_one] at hp; exact hp
omit p' h hp hw in
lemma arty {D:ℕ}{u:ℝ}(hx:0 ≤ u)(he:u<1)(hk:k≤ D)(P:Patch):∃ r a:ℝ,
      EndPrice D P.L<r∧ EndPrice D P.L<a ∧ u*r ≤ a∧(∀ i<k, r < lapPrice P.L i)∧(∀ i< D+1,k≤ i→ lapPrice P.L i < r)∧(∀ i<k+1,a < lapPrice P.L i)∧∀ i < D+1,k+1 ≤ i→lapPrice P.L i<a:=by -- parameters omit!
      let μ:=lapPrice P.L
      let z:= μ k; have hz:0<z:=EndFare ..; let s:= if k<D then μ (k+1) else EndPrice D P.L; have hh:u*z < z:=by nlinarith only [hx,he,hz]
      have hv: s<z:=by unfold s;split;apply stairPrice _ _ _ (by omega) P.coarse; exact arrival _ _ _ hk P.coarse
      obtain ⟨a,ha,hx'⟩:=exists_between (max_lt hh hv); let q:=if k>0 then μ (k-1) else z+1; have hg:z<q:=by unfold q; split; exact stairPrice _ _ _ (by omega) P.coarse; linarith
      let x:= min (a-u*z) (q-z); have hs₁:u*z< a:=lt_of_le_of_lt (le_max_left ..) ha; have hs₂:s<a:=lt_of_le_of_lt (le_max_right ..) ha; have ht:0<x:=lt_min (by linarith) (by linarith); obtain ⟨r,H,H'⟩:=exists_between ht; have hu:=lt_of_lt_of_le H' (show x ≤ q-z from min_le_right ..); have hy:=lt_of_lt_of_le H' (show x ≤ a-u*z from min_le_left ..)
      refine ⟨z+r,a,lt_of_lt_of_le (arrival _ _ _ hk P.coarse) (le_add_of_nonneg_right H.le), ?_, ?_, ?_, ?_,?_,?_⟩
      · apply lt_of_le_of_lt _ hs₂; unfold s; split; exact (arrival P.L (k+1) D (by omega) P.coarse).le; rfl
      · nlinarith
      · intro i hi; apply lt_of_lt_of_le (show z+r < q from by linarith); unfold q; rw [if_pos (by omega)]; by_cases he:k-1=i;rw [he]; exact (stairPrice P.L _ _ (by omega) P.coarse).le
      · intro i _ h; obtain h|h:=Nat.lt_or_eq_of_le h; apply (stairPrice P.L _ _ h P.coarse).trans; linarith only [show 0<r from H, show μ k=z from rfl]; subst i; exact lt_add_of_pos_right _ H
      · intro i hi; apply hx'.trans_le; by_cases he:i=k; subst i;rfl; exact (stairPrice P.L i k (by omega) P.coarse).le
      intro i hi h; apply lt_of_le_of_lt _ hs₂; unfold s; rw [if_pos (by omega)]; by_cases he:i=k+1; subst i;rfl; exact (stairPrice _ _ _ (by omega) P.coarse).le
lemma framing (ht:Crest G P K.K m)(hx:∀ i,τ i ≤ m) [Nonempty Y!] :∃ V, ∀ i:Fin (e+1),∃ r θ:ℝ, Eave L! V (Turns hp) Sailing.cost r θ θC i.val:=by -- notation.Nonempty.
      obtain ⟨V,hV,he,hv⟩:= FlapZen (T:=T) (p:=p) (b:=b) h hp p' hw ht hx; refine ⟨V,fun i=>?_⟩; obtain ⟨r,a,hp',he',hy,hx,hν,hω,hu⟩:= arty thetaC.1.le thetaC.2 (show i.val≤ e by omega) P
      exact ⟨r,a, (show Eave L! V (Turns hp) Sailing.cost r a θC i.val from ⟨Nat.succ_pos _,fun i=>i.fits,mul_comm r θC ▸ hy,thetaC.1.le,he,hV,fun k i=> statute hp p' hw h _ i,i.isLt,fun _=>⟨hp',i.isLt.le,hx,fun i hi h=> hν i h hi⟩,fun _=>⟨he',i.isLt,hω,fun i hi h=>hu i h hi⟩⟩)⟩
end YM.OPE.Drift
