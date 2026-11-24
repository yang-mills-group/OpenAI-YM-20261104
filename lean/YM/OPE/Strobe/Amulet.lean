import YM.OPE.Vitrines.Clasp
import YM.OPE.Strobe.Noon
/-! # Which near signal. Other alternative uses constant. Paint EXACT restoration. -/
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
local notation "c" => C.side k p
local notation "α" => alto C.path k d
local notation "s" => C.factory d N p
local notation "γ" => ((1,false):Motion)
local notation "Z" => C.localSection d
local notation "Q" v=> parcel C d k N p (v)
local notation "κ" i=> Real.sqrt (C.path.levels.clock.forcedAllowance (i))
local notation "F₁" => C.labels.level d
local notation "θ" i => (C.path.levels.params (i)).columns
open Vitrines Therm
variable {u:ℕ} {v:C.label d} (T₀ : Citizen C W r D)

-- reassuring token size.Numerical certificate uses only this x no rank.
lemma mintedLabel (x:C.label d): Spindle.paid C d k N p x=‖alto C.path k d‖*((C.labels.level d).coeffSize (Q x).x) := Size.smul ..
/-- local marked subtraction at mesh. Not mere Born fields; includes exact masks. -/
def bead (C:Family G)(d k N p:ℕ)(u:ℕ)(v:C.label d)(x:Site (C.side k p)): Config G (C.side k p) → ℂ:= radiant (alto C.path k d) (1,false) x (enamel (C.localSection d) (C.path.rep N p k) (parcel C d k N p v) u)
def cameo (C:Family G)(d k N p:ℕ)(v:C.label d):= alto C.path k d*(parcel C d k N p v).x 0
def payment (C:Family G)(k u:ℕ)(v:ℝ)(ice:Bool):= 2*(C.path.levels.params k).columns*v*if ice then Real.exp (-2*(u:ℝ))+Real.sqrt (C.path.levels.clock.forcedAllowance k) else Real.exp 100+1+Real.sqrt (C.path.levels.clock.forcedAllowance k)
def omen (C:Family G)(d k u:ℕ):= BasisCost.extent (C.localSection d)+Therm.Stove.eroom (C.path.levels.budget k) u
variable {ρ w:ℝ} {X:Lamp G (C.side k p)} (ice:Bool) (u:ℕ) {M : Extra.Histories.Music (C.labels.level d) C.path N p}
def betaDrop (C:Family G)(d k N p u:ℕ)(v:C.label d)(x:Site (C.side k p))(ice:Bool) := if ice then -bead C d k N p u v x else (fun _:Config G (C.side k p)=> -cameo C d k N p v)
def flickVolume {n:Side} (u : Config G n→ℂ)(X:Lamp G n): Lamp G n:=⟨X.watch+u,X.sparks,X.lit⟩
variable (o:∀ i,Site (C.side i p))
local notation "y" => payment C k u
include T₀ H
section
lemma prizeMe (x : Site (C.side k p))(hz:C.ref 0< k)(hk:C.ref d ≤ k)(ht:k < N)(hv: Spindle.paid C d k N p v ≤ ρ) (hA:Patrol.Lyrics M W (waybill C.path.levels) D)(he:o k=x)
    (hp:X.watch=soarF C.path Z N p M ((C.factory d N p).terminal.symm v) (1,false) o k)
    (hP:X.rays (C.path.rep N p k)=soarK C.path N p M ((C.factory d N p).terminal.symm v) (1,false) o k) : (flickVolume (betaDrop C d k N p u v x ice) X).Flex (C.path.rep N p k) x (payment C k u ρ ice):=by
    let A:=H.strong (p:=p) hz ht.le; let b:= (s).terminal.symm v; let P':= (s).entries k b; let D':= (F₁); let e:=P'.exponentialEntry 0 (Z) (R k); let B:= (Z).footprint (0:Site c); let a:= θ k; let t:= a*D'.coeffSize (D'.core P'.x); let lil := Real.exp (-2*(u:ℝ)); have h:= H.seed.calibrated d N p (hk.trans ht.le); have h₀:= H.seed.wilson.represents N p k ht.le; have hθ:= T₀.torches d N p k hk ht b; have hf:P'.Format 0 C.params (R k):= h.format k hk ht.le _; have hh:P'.remBound 0 (R k) (κ k) t:= h.cap k hk ht.le _; have he':0 ≤ t:=Blown.price hθ; have hp':(M.tone k).plays b=P':= (by unfold P'; rw [hA.entries]; rfl); let K:= profile (R k|>.activities) P'.forced; obtain ⟨π⟩:= h₀.good.labels.moves (1:Signed) x
    have h₁:X.watch=radiant α γ x e:=by unfold soarF at hp; rw [he] at hp; rw [hp, show _= P' from hp'];
    have h₂:X.rays (R k)= α • floatUp γ x K:= by unfold soarK at hP; rw [he] at hP; rw [hP,show _= P' from hp']; rfl
    have ha:0≤a:= zero_le_one.trans (C.path.levels.params k).columns_ge; have hT:‖α‖*t ≤ a*ρ :=by apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rotate_core D' _) ha) (norm_nonneg _)); rw [mul_left_comm ‖_‖]; exact mul_le_mul_of_nonneg_left ((mintedLabel (N:=N) (k:=k) (p:=p) v).symm.trans_le hv) ha
    have hl:0 ≤ lil + κ k:= add_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _); let U:= (R k); change Blade (R k) x (X.watch+betaDrop C d k N p u v x ice) (X.rays _) 0 (y ρ ice); rw [h₁,h₂]; unfold payment betaDrop; split
    · let w:= enamel Z U P' u; have hT': Blade U 0 (e-w) K 0 (2*(lil+κ k)*t):= silver Z A hf hh hθ u; have hs: radiant α γ x e + (-bead C d k N p u v x)= α • stepUp γ x (e-w):= by funext i; change α*_ + -(α * w _)= α*(e (pull 1 x i)-w (pull 1 x i)); rw [mul_sub,sub_eq_add_neg]; rfl
      rw [hs]; apply Blade.more (g:=α • stepUp γ x (e-w)) (mul_zero α ▸ (conical x π hT').rate α) _ ; convert mul_le_mul_of_nonneg_left hT (mul_nonneg zero_le_two hl) using 1 <;> simp (config := {failIfUnchanged:=false}) only [lil,a] <;>  (first|rfl|ring)
    · let w(x:Config G c):= P'.x 0; let l':= U.p.mass B t+(1+(κ k))*t; have hs: radiant α γ x e + (fun _=> -cameo C d k N p v)=α • stepUp γ x (e-w):= by
         funext i; unfold cameo; change α*_ + -(α * P'.x 0) = α*(e (pull 1 x i)-w (pull 1 x i));rw [mul_sub,sub_eq_add_neg]; rfl
      have hT': Blade U 0 (e-w) K 0 (2*l'):= gold Z A hf hh hθ (Finset.mem_image.mpr ⟨0,(H.seed.sections d).anchored, by simp⟩) (fun i=>by unfold U; rw [h₀.vac]; exact H.seed.priced d k p hk 0 i)
      rw [hs]; apply Blade.more (g:=α • stepUp γ x (e-w)) (mul_zero α ▸ (conical x π hT').rate α) _
      let R' := Real.exp 100+1+ κ k; have hx:0≤R':=by unfold R'; positivity
      refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show l' ≤ R'*t from ?_) zero_le_two) (norm_nonneg _)).trans (?_); swap; · convert mul_le_mul_of_nonneg_left hT (mul_nonneg zero_le_two hx) using 1 <;> simp only [R',a] <;> ring
      obtain ⟨q,_,_,_,hv',_⟩:= H.cuts.system.costs.heights d k k p hk (le_refl k); unfold l' BudgetPoint.mass U R'
      apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) he') _) (le_of_eq (by ring)); rw [h₀.vac,T₀.price]; apply le_trans (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (le_of_eq (mul_one _)); exact_mod_cast hv'
end
end YM.OPE.Strobe

