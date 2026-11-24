import YM.OPE.Strobe.Helix
/-! # One rendezvous at charged μ. Multi probe k.Scopes are on history; one bare moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
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
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
local notation "X" => (C.path.levels.clock.hatBeta)
open GridApprox
local notation "α" => alto C.path k d
variable (v w:C.label d)(a:ℕ)(o:Site (C.side k p))(he:k≤N)(hf:C.ref d≤k)
def abrade (C:Family G)(v:C.label d)(N k p:ℕ)(x:Site (C.side k p))(he:k≤N) := C.O N p v (anchor C.S p he x)
local notation "P₁" => (abrade C v N k p)
local notation "Q₁" => (abrade C w N k p)
local notation "T'" => writeF C v N k p a
local notation "S" => GridApprox.backTo C.path N p
local notation "t" => C.beta N p
local notation "p*" => bead C d k N p a
local notation "L" => (law G (C.side N p) (t))
variable {c c' s':ℝ}
def scenePair (C:Family G) (v w:C.label d)(k N p a:ℕ)(o:Site (C.side k p)):= ∫ U, bead C d k N p a v 0 U * bead C d k N p a w o U ∂ (Therm.scene C.path N p k)
include H hf he
lemma write_e (ice:Bool) : Envelope (writeF C v N k p a o he ice) := (Envelope.compactC (C.continuousO ..)).addC (backTo_env C.path N p he (cylinder_env (dropped H o v hf he a ice)))
lemma write_move : moment (C.beta N p) (writeF C v N k p a o he true) = moment (C.beta N p) (writeF C v N k p a 0 he true):= by
    let r:= (0:Site (C.side k p)); let u:= anchor C.S p he o; let f:=betaDrop C d k N p a v 0 true
    have hξ : betaDrop C d k N p a v o true = f ∘ pull 1 o:= by
       unfold f betaDrop bead radiant; simp only [stepid,↓reduceIte]; rfl
    let hV:= (write_e (p:=p) H v a 0 he hf true) -- shadow hf error fix
    rw [← moment_pull t 1 u (T' 0 he true) (hV.integrableC _ : Integrable _ (law G (C.side N p) _))]; apply congr_arg (moment _); unfold writeF; rw [hξ];
    have hA: o=anchor C.S p (le_refl k) o:= ((there o).symm.trans (vect C k p k o le_rfl)); have hp:= backTo_orient C.path N p (h:=k) le_rfl he o (1:Signed) (show Envelope f from cylinder_env (dropped H (0:Site (C.side k p)) v hf he a true)); -- dropped takes v explicit. syntax.
    rw [← hA] at hp; rw [hp]; funext U; change C.O N p v u U + _= C.O N p v _ (pull 1 u U)+_; rw [show anchor C.S p he 0=0 from (C.S.toDepth he p).root.map_zero,pull_one,C.translation,zero_add]; rfl
local notation "a!" => cameo C d k N p
omit H hf in
lemma erased (ice:Bool) : writeF C v N k p a o he ice= (if ice then P₁ o he-backTo C.path N p he (bead C d k N p a v o) else P₁ o he-(fun _=> a! v)):=by
    unfold writeF betaDrop abrade; split_ifs; swap;· rw [GridApprox.backTo_const C.path N p he (-(a! v)),sub_eq_add_neg];rfl
    rw [sub_eq_add_neg,← neg_one_smul ℂ (bead C d k N p a v o), ProofPorts.GridRealModelEstimates.backTo_linear,neg_one_smul]
private lemma twoBack (hx:2*muzzle C.path.levels k (omen C d k a)<separation o 0) : backTo C.path N p he (bead C d k N p a v (0:Site (C.side k p))* (bead C d k N p a w o)) = backTo C.path N p he (bead C d k N p a v (0:Site (C.side k p))) * backTo C.path N p he (bead C d k N p a w o):=by
    let psX(x:Bool):= if x then bead C d k N p a w o else bead C d k N p a v (0:Site (C.side k p)); let g(b:Bool):= if b then o else (0:Site (C.side k p)); have hh(x): Interior (GridApprox.window (g x) (omen C d k a)) (psX x):= by cases x; exact bead_local H _ _ hf he a; exact bead_local H _ _ hf he a
    have hX := backs_many C.path _ N p _ _ g univ hh (fun i j=> by cases i <;> cases j <;> intro h; exacts [False.elim (h rfl),by unfold g; simpa [separation_comm] using hx, hx, False.elim (h rfl)]) he; have hB {x:Side} (F:Bool→ Config G x→ℂ): fineJob F univ=F false*F true:= by unfold fineJob;funext i; simp [mul_comm] -- fix
    rw [hB,hB] at hX; exact hX
lemma polarized (hx:2*muzzle C.path.levels k (omen C d k a)<separation o 0)
    (hf₁:Spindle.paid C d k N p v ≤ c)(hf₂:Spindle.paid C d k N p w ≤ c)
    (h₁ : (∀ v₁ v₂:Bool,v₁=true∨v₂=true → ‖moment (C.beta N p) (writeF C v N k p a 0 he v₁ * writeF C w N k p a o he v₂)‖≤ c'))
    (h₂: ‖moment (C.beta N p) (writeF C v N k p a 0 he true)‖≤ s')(h₃: ‖moment (C.beta N p) (writeF C w N k p a 0 he true)‖≤ s') : ‖moment (C.beta N p) (abrade C v N k p 0 he * abrade C w N k p o he) - scenePair C v w k N p a o‖ ≤ 3*c'+2*c*s':=by
    let x:=P₁ 0 he; let y:=Q₁ o he; let G':=S he (p* v 0); let D':=S he (p* w o);
    let M':= Therm.scene C.path N p k; let u (v':Bool):= writeF C v N k p a 0 he v'; let u' (v':Bool):= writeF C w N k p a o he v'; have hv(ice):= write_e (p:=p) H v a 0 he hf ice; have hw(i):= write_e H w a o he hf i; have h₀(v)(q): Integrable (u v*u' q) L:= ((hv v).mulC (hw q)).integrableC _
    have hEq:(∫ W,G' W*D' W ∂L) = scenePair C v w k N p a o:=by
       let Pe:=bead C d k N p a v 0; let Q:=bead C d k N p a w o; have hP:= cylinder_env (bead_local (p:=p) H 0 v hf he a); have hQ:=cylinder_env (bead_local H o w hf he a); have he':= (twoBack H v w a o he hf hx).symm; change moment (C.beta N p) (G'*D') = _; rw [show G'*D'= _ from he']; exact (Therm.onstage H.seed.wilson _ ((GridApprox.backTo_env _ _ _ _ (hP.mulC hQ)).integrableC _)).symm.trans (Therm.retro H.seed.wilson he le_rfl (Pe*Q) (hP.mulC hQ))
    let z:= u true; let z':= u' true; let q:=u false; let q':=u' false; let b:= -(z*z'); have hp : Envelope (u true):= hv _; have hp':Envelope (u' true):= hw _; let e:= a! v; let f:= a! w; let V₀:=(L)
    have hy : x*y = G'*D'+ ( (z*q'+q*z')+b)+(f • z+ e • z'):=by funext i; have hx₁:= erased (p:=p) (C:=C) v a 0 he true; rw [if_pos rfl] at hx₁; have hx₂:= erased (p:=p) (C:=C) v a 0 he false; rw [if_neg (by decide)] at hx₂; have hx₃:= erased w a o he true; rw [if_pos rfl] at hx₃; have hx₄:= erased w a o he false; rw [if_neg (by decide)] at hx₄; unfold b z z' q q' u u'; simp only [hx₁,hx₂,hx₃,hx₄,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,Pi.sub_apply]; unfold x y G' D' e f; ring
    let ξ(c:Config G (C.side N p)→ ℂ):= moment (C.beta  N p) c; have i₁:=hp.integrableC (L); have i₂:=hp'.integrableC (L); let Tq:=f • z+ e • z'; have hT: Integrable Tq L:= (i₁.smul _).add (i₂.smul _); have hr: Integrable (G'*D') L:= ((GridApprox.backTo_env C.path N p he (cylinder_env (bead_local (p:=p) H 0 v hf he a))).mulC (backTo_env C.path N p he (cylinder_env (bead_local H o w hf he a)))).integrableC _
    have hΨ : moment (C.beta N p) (x*y)= ξ (G'*D') + ((ξ (z*q')+ ξ (q*z'))- ξ (z*z'))+(f*ξ z + e*ξ z'):=by
       have μadd {u v:Config G (C.side N p)→ℂ}(hx:Integrable u (L))(hp:Integrable v (L)) : ξ (u+v)= ξ u+ξ v:= integral_add hx hp
       change ξ (x*y) = _
       rw [hy]; rw [μadd (hr.add (((h₀ true false).add (h₀ false true)).add ((h₀ true true).neg))) hT,μadd hr (((h₀ true false).add (h₀ false true)).add ((h₀ true true).neg)),μadd ((h₀ true false).add (h₀ false true)) (h₀ true true|>.neg),μadd (h₀ true false) (h₀ false true),μadd (i₁.smul f) (i₂.smul e)]; unfold ξ moment; simp only [Pi.neg_apply, Pi.smul_apply,smul_eq_mul,integral_neg,integral_const_mul,sub_eq_add_neg]; rfl
    change ‖moment (C.beta N p) (x*y)- scenePair C v w k N p a o‖≤ _; rw [hΨ,← show ξ (G'*D') = scenePair C v w k N p a o from hEq, add_assoc, add_sub_cancel_left] -- edit easier abel
    rw [← write_move H w a o he hf] at h₃; have H₁:= cameo_price v hf₁; have H₂:= cameo_price w hf₂; have hc:0 ≤ c:= (norm_nonneg _).trans H₁
    have Hf : ‖(f*ξ z + e*ξ z')‖ ≤ c*s'+c*s':= by
       refine le_trans (norm_add_le ..) ?_; rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul H₂ h₂ (norm_nonneg _) hc) (mul_le_mul H₁ h₃ (norm_nonneg _) hc)
    refine (le_trans ((norm_add_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (h₁ true false (Or.inl rfl)) (h₁ false true (Or.inr rfl)))) (h₁ true true (Or.inl rfl)))) Hf)) (le_of_eq (by ring)))
end YM.OPE.Strobe

