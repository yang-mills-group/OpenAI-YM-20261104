import YM.OPE.Compatible.Mould.Dense
/-!
# Radar.Prel supports. visibility pressure. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
namespace Topic
open Balsam Nestle StageLight Pert.Full
def wagonN (n:ℕ):Side:=⟨2*n+2,by omega⟩
lemma wagon_h (n:ℕ):Even (wagonN n).val:=⟨n+1,by unfold wagonN;dsimp;omega⟩
lemma wagon_v : Ncap wagonN atTop:= tendsto_atTop_mono (fun n=>by change n ≤ 2*n+2;omega) tendsto_id
end Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
namespace Topic
variable {u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}
open Balsam Nestle StageLight Pert.Full
variable (he:e<l+1)
variable (hB: l+l<k) (ht:∀ i,τ i≤m)(hq:∀ i,Rise.stamp' d G k+44 ≤ τ i)
lemma ghostPower (Y:Lance X)(x:Bead G l e)(hp:x∉ Ghost G l e)(hB: l+l<k) (ht:∀ i,τ i≤m)(hv:∀ i,Rise.stamp' d G k+44 ≤ τ i):∃ n:Side,∃ V:Even n.val,let Q:=wrap n (skew a); let P':=wrap n (Point a); Attest G P d k e l m τ n ∧ Pins K P Q P'∧0 <Zpin Hp Z a he V Q P' x x :=by
      have ht' :∀ᶠ i in atTop,Attest G P d k e l m τ (wagonN i):= (wagon_v.eventually (eventually_ge_atTop (barrier P))).mono (fun i hi=>⟨hi,ht,hv,hB⟩); obtain ⟨s,hS,hX⟩:=barPos H hs X B Z.station D₀ (Z.bill e he) a Hp Y (t:=wagonN) wagon_h wagon_v ht' x; have hh:= hX.eventually (lt_mem_nhds (hS hp)); obtain ⟨n,H⟩:= (hh.and (ht'.and (togetherH (K:=K) (P:=P) (skew a) (Point a) wagonN wagon_v (slanted a) wagon_h))).exists; exact ⟨wagonN n,wagon_h _,H.2.1,H.2.2,H.1⟩
include hB ht hq
lemma Nem (pY:Mint Z e)(x:Phase)(hp:pY∈ Dross Hp Z a e)(hx:trims x.val pY.val)(Y:Lance X): UΦ Z he pY x∈ Ghost G l e:=by
      obtain ⟨p,h,hT⟩:= porShift Z he pY x hx
      by_contra H'; rw [hT] at H'; obtain ⟨n,v,hV,hP,Hq⟩:= ghostPower Hp Z a he Y _ H' hB ht hq; rw [ZFore Hp Z a he p v _ _ hV hP] at Hq
      have ht':= gyro Hp Z a he v _ _ hV hP x p p; rw[← h,(skep Hp Z a _ _ _ _ _ _ hp hV.base hP).1] at ht'; have hx: (0:Token).seq x.val=0:=by fin_cases x<;>rfl
      exact (ne_of_gt Hq) (ht'.symm.trans hx)
end Topic
end YM.OPE.Stroke
