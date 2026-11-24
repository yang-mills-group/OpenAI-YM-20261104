import YM.OPE.Strobe.Show
import YM.OPE.Strobe.Flick
import YM.OPE.Strobe.Rosy
/-! # Couple post-permissive spacing at k on gust-birth before grouped spend -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℕ→ℝ} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}
local notation "Z" => royal C m p
local notation "r*" => stepUp
private lemma fuze {X:I→Lamp G (C.side k p)} {P₁:I→Lamp G (C.side k p)} (A':I→ Config G (C.side k p)→ℂ) {o:I→Site (C.side k p)} {w:I→ℝ} {Q:Config G (C.side k p)→ Marker.Poly (Names (Site (C.side m p)) I)} (h: Fleet (Z k) (C.path.rep N p k) Q o P₁ w) (hr:∀ i,(X i).rays (R k)= (P₁ i).rays (R k)) (he:∀ i,(X i).watch=(P₁ i).watch+A' i)(g:Integrable (couple Q ((Z k).calls A')) (prior G _)) : Fleet (Z k) (C.path.rep N p k) (couple Q ((Z k).calls A')) o X w:=by
    obtain ⟨S,K,hζ,hμ,hT,hσ,hQ⟩:=h.sem; have hx: (Z k).lamp X=(Z k).lamp P₁+(Z k).calls A':=by
       funext i; unfold Brigade.lamp Brigade.calls; simp only [he,Pi.add_apply]; split; rfl; exact funext (fun U=> Motion.scalar_add ..)
    have hW: (Z k).ray (R k) X=(Z k).ray (R k) P₁:=by unfold Brigade.ray; simp_rw [hr]
    let ι:= Names V I; let A:= (Z k).calls A'
    refine ⟨hx.symm ▸ hW.symm ▸ (?_:Serves (R k) ((Z k).lamp P₁+A) ((Z k).ray (R k) P₁) _ (Z k|>.head) (Z k|>.spin) (Z k|>.center) (Z k|>.roll) ((Z k).place o) (w ∘ Prod.snd) ((R k).p.supportExponent-3) 1),g,(by exact h.secure)⟩
    refine ⟨S,K,hζ,hμ,hT,hσ,?_⟩; change couple Q A= _;
    rw [hQ]; funext U; unfold Accent.couple restore; let R₁:= R k; let u:= Mach (ι) (fun i=>((Z k).lamp P₁ i) U)+ ∑ i,S i U; let l:=Mach (ι) (fun i=>A i U); let V':= (Z k).lamp P₁
    have hp : Mach (ι) (fun i=>(V'+A) i U)+ ∑ i,S i U=u+l:=by
       unfold Mach; simp only [Pi.add_apply,Extra.Trajectories.send_add, sum_add_distrib]; unfold u l V' Mach; abel
    rw [hp,Extra.Trajectories.pass_add (show u.part ((ι).quiet)=0 from by unfold u; rw [Poly.part_plus,Accent.mute,Poly.part_sum,zero_add]; exact sum_eq_zero (fun i _=>Accent.hop _ _ ((hζ.exp i).2 U))) (show l.part ((ι).quiet)=0 from Accent.mute _ _), smul_mul_assoc]; apply congr_arg; unfold u l; rw [mul_right_comm]
-- prewarm.R not spacing at final rung; Band k N. Last push directly Repegs at output with amplified budget built later.
include H
variable (E: Band C o r k N m)(hr:m≤k)(hk:C.ref 0<k)(hN:k<N)
variable {y:I→ℝ}{a:ℕ}
local notation "X" i=> (fun j=>o j (i))
local notation "v" i=> (fun j=>w j (i))
local notation "s*" i => ((Z i).place (fun j=>o j (i)))
include E hr hk hN
lemma flared (A':I→ Config G (C.side k p)→ℂ) (S:I→Lamp G (C.side k p)) (hQ:∀ i,Patent C N p (o i N) (Y i N) (F i) (w i N)) (hx:∀ l, Drive C.path k N N p (o l) (w l) D (Y l) le_rfl) (hw:∀ l i,k ≤ i → i≤N → 0<w l i) (hV:∀ i,k < i→ i<N →∀ a,near C.path.levels i*w a i ≤ w a (i+1))(hω:Occupancy (s* N) (r N))
    (hP:Repegs (s* k) (C.path.levels.budget k).B (fun j=>renal C.path.levels k*w j.2 (k+1)) (y ∘ Prod.snd) (1/2) 1 (Names (Site (C.side m p)) I))(hy:∀ i,0<y i)
    (hp:∀ i j,i≠j→ 2*muzzle C.path.levels k a < separation ((s* k) i) ((s* k) j)) (hX:∀ i, Interior (GridApprox.window (o i k) a) (A' i))(hf:∀ i,(S i).rays (R k)= (Y i k).rays (R k))(he:∀ i,(S i).watch=(Y i k).watch+A' i): ∃ Q,ShowF C N p m k Q (F+(fun i=>GridApprox.backTo C.path N p hN.le (A' i))) (X k) y S:=by
    let F' := (Z N).calls F; let Xt := Names (Site (C.side m p)) I
    let Q:= birth Xt (R N) F'; let Q':=gust C.path N p N Q k hN.le; let Z':=gust C.path N p N Q (k+1) hN; let W':=(Z k|>.place (X k)); let t':= (T).clock.op k p; have ho:t'.ratio.parent ∘ (X (k+1))= (X k):= funext fun i=> E.clock k le_rfl hN i
    have hB:=Yarn.rosate (x:=F) H (hr.trans hN.le) hω (fun i=>hw i N hN.le le_rfl) hQ -- parameter `x` not F!
    have hZ := run_car H E hr hk hN (le_refl N) hB hx hw hV k.lt_succ_self hN
    have hA: Fleet (Z k) (R k) Q' (X k) (fun i=> Y i k) y :=by
       unfold Q'; rw [gust_step C.path N p N Q hN,← ho]; refine Fleet.steady (w:= v (k+1)) _ H.seed.wilson hN H.thor hk.le ((climbR (C:=C) (p:=p) hr).symm ▸ hZ.fleet) (ho.symm ▸ E.crowd k le_rfl hN) (fun i=> hx i|>.drives k le_rfl hN) hy (ho.symm ▸ hP)
    let A:= (Z k).calls A'; let Q'':= Accent.couple Q' A; let f:= fun i=> GridApprox.backTo C.path N p hN.le (A' i)
    have hz : Sings C.path N p k Q'' ((Z N).calls (F+f)):=by
       have hX' := Sings.jargon hN.le A (fun t=>backs_many _ a _ _ _ _ _ t (wind hX) hp hN.le) (fun i=> GridApprox.cylinder_env (wind («P»:=Z k) hX i)) hB.script.cost H.seed.wilson hB.fleet.pay -- ambiguous
       have hv : (Z N).calls (F+f) = F'+fun q=> GridApprox.backTo C.path N p hN.le (A q) :=by
          funext i; unfold F' f A; simp_rw [callsR hr, Pi.add_apply, GridApprox.backTo_copy C.path N p hr hN.le _ (GridApprox.cylinder_env (hX _)), callsR (hr.trans hN.le)]; -- `simp_rw callsR hr` which calls RHS.Unify.
          unfold Tiling.copy; funext U; split <;> simp
       rw [hv]; exact hX'
    exact ⟨Q'',hz,fuze A' hA hf he hz.budget⟩
end YM.OPE.Strobe

