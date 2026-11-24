import YM.OPE.Strobe.Amulet
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
-- all labels from FRAME fixed horizon for now; subtype lower imported with coal; raw descriptors all same. Sym doesn't need local comp.Lights.
local notation "s" => C.factory d N p
local notation "α" => alto C.path k d
local notation "γ" => ((1,false):Motion)
variable {x w:I→ℝ} {f : I→ C.label d}{S:Extra.Histories.Music (C.labels.level d) C.path N p} {u K:ℕ} {ice : I → Bool}{ρ :ℝ}
include H
local notation "u!" => omen C d k u
local notation "o!" i => (fun a=> o a (i))
open Vitrines GridApprox
lemma bead_local (x:Site (C.side k p))(f:C.label d)(hk:C.ref d ≤ k)(he:k ≤ N) (u:ℕ) : Interior (GridApprox.window x (omen C d k u)) (bead C d k N p u f x):=by
   let v:=Spindle.parcel C d k N p f; let U:= enamel (C.localSection d) (R k) v u; let b:= omen C d k u; have hx:= H.seed.calibrated d N p (hk.trans he); have hv:v.Format 0 C.params (R k):= hx.format k hk he _; have hp:= enamel_local (C.localSection d) hv (hx.cap k hk he _) (H.seed.sections d) u; rw [show (C.path.rep N p k).p = _ from (H.seed.wilson.represents _ _ _ he).vac] at hp; have hh: Interior (GridApprox.window 0 b) U:= island _ |>.symm ▸ hp; have hz:= hh.unchanged _ _ (window_affine _ x 1); rw [show affine 1 x 0=x from by simp [affine]] at hz; exact hz.scale _
lemma dropped (x:Site (C.side k p))(f:C.label d)(hk:C.ref d ≤ k)(he:k ≤ N) (u:ℕ)(ice:Bool) : Interior (GridApprox.window x (omen C d k u)) (betaDrop C d k N p u f x ice):=by unfold betaDrop; split; rw [show -bead C d k N p u f x= (-1:ℂ) • bead C d k N p u f x from by simp]; exact (bead_local H x f hk he u).scale _; exact Interior.constant _ _
omit H in
lemma cameo_price (f':C.label d) (he: Spindle.paid C d k N p f' ≤ ρ): ‖cameo C d k N p f'‖ ≤ ρ:=by rw [mintedLabel] at he; unfold cameo; rw [norm_mul]; exact le_trans (mul_le_mul_of_nonneg_left (BasisCost.coord_le _ _) (norm_nonneg _)) he
local notation "U" => (fun i=>C.O N p (f i) (o i N))
local notation "Q'" => (fun i=> betaDrop C d k N p u (f i) (o i k) (ice i))
local notation "L" => ((Z k).place (o! k))
local notation "P'" => renal C.path.levels k
lemma ember (T₀ : Citizen C W r D)
    (E:Band C o r k N m)(hm:m≤k)(hk:k<N)(hl:C.ref 0 < k) (he:C.ref d ≤ k)(hω:Occupancy ((Z N).place (o! N)) (r N)) (hA:∀ a,∀ i,k ≤ i→ i < N→ o a (i+1)= (C.path.levels.clock.op i p).ratio.embed (o a i)) (hL:∀ a, Spindle.paid C d k N p (f a) ≤ ρ)(hw:∀ a,0<w a)(hv:∀ a,w a*ρ ≤ ζ d k) (hy:∀ a,0<x a) (ht: ∀ i j, i≠j→ 2*muzzle C.path.levels k (omen C d k u)< separation ((L) i) ((L) j))
    (hq:Repegs L (C.path.levels.budget k).B (fun j=> renal C.path.levels k*(near C.path.levels k*w j.snd)) (x ∘ Prod.snd) (1/2) 1 (Names (Site (C.side m p)) I))(hC:∀ a,payment C k u ρ (ice a) ≤ 4*(1/x a)): Shown C N p m k (fun i=> C.O N p (f i) (o i N)+ GridApprox.backTo C.path N p hk.le (betaDrop C d k N p u (f i) (o i k) (ice i))) (fun i=> o i k) x:=by
   obtain ⟨S,hS⟩:= Yarn.curtain H (p:=p) he hk.le; let X(i) := (s).terminal.symm (f i); let v₀ (i):= stair η (w i) k
   choose V' hV hP hT using fun i=> Yarn.first_wish H (o i) (hA i) hS he hk.le (hw i) (by unfold X; rw [Yarn.bond_paid he hk.le hS]; exact le_trans (mul_le_mul_of_nonneg_left (hL i) (hw i|>.le)) (hv i): w i*bond C.path N p S k (X i) ≤ ζ d k) -- explicit X def rw needs
   let W':= Q'; let z i:= flickVolume (W' i) (V' i k); have hZ(i): (z i).Flex (R k) (o i k) (4*(1/x i)):= Blade.more (prizeMe (v:=f i) H T₀ (ice i) u (o i) (o i k) hl he hk (hL i) hS rfl (hT i k le_rfl hk.le|>.1) (hT i k le_rfl hk.le|>.2)) (hC i)
   let F' := U; have hp(i): Patent C N p (o i N) (V' i N) (F' i) (v₀ i N):=by have hx:= hP i; rw [show (C.factory d N p).terminal (X i)=f i from LinearEquiv.apply_symm_apply ..] at hx; exact hx
   have hF := flared H E hm hl hk W' z hp hV (fun a i _ _=>H.protectors _ (hw a) _ i) (fun i hi he a=> (H.fall_march hi.le).symm.le) hω (y:=x) (show Repegs _ _ (fun j:V × I=> P'*v₀ j.2 (k+1)) _ _ _ _ from by unfold v₀; simp_rw [H.fall_march (Nat.le_refl k),H.anchor_march (hw _)]; exact hq) hy ht (fun i=> dropped H _ _ he hk.le ..) (fun _=>rfl) (fun _=>rfl) -- x named y. fallback
   exact ⟨hF.choose,z,hF.choose_spec,hZ⟩ -- rev ?_
end YM.OPE.Strobe

