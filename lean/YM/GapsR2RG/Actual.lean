import YM.GapsR2RG.MomentPatch
import YM.OPE.Single
import YM.EveryPhase.Summit
import YM.Pert.Asymptotics.RawAxis
/-!
# Earnt actual annular product bank (before Gaussian/diagram identification).

This does not fit formal Wilson coefficients to the answer. It reads fine
Wilson sources at descendants `anchor` of points in the reported mesh and
compares to products of the actual localized columns (`bead`), averaged TOGETHER
on `Therm.scene C.path N p k`, *without replacing the unmarked vacuum*.
All dirty configurations included. It is only a signed/correlation comparison,
not the arbitrary full-density norm recurrence (see ledgers). The true density
representations used by `flaredMixed` preserve all joint sectors under that one
trajectory, then test a stochastic difference at the price of true/error slots,
merge and continue down to fixed stop (in `decay`), using replication there.

Witness constructor adapted from `YM.OPE.through_final`. No claimed identity
with separate full-volume or RG12/17 richer schedules. Strict consumer below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsR2RG
open OPE OPE.Yarn OPE.Strobe
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol OPE.Loom
open Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Next.Rank.Station Spec
variable {J:Type}[Fintype J][DecidableEq J]{E:ℕ}{G:Gauge}{C:Family G}
variable {W r D}{σ γ:ℕ→ℝ} (H:Yarn.Tune C W r D σ γ)
local notation "gB" => C.path.levels.clock.hatBeta
set_option quotPrecheck false
local notation "B#"=> (fun i=>(C.path.levels.budget i).B)
local notation "z*" => Pert.Asymptotics.regulatorRun C
include H
lemma bandRun {i p N}(hi:i≤N): 0<(z*) N p i ∧ (gB i)⁻¹ ≤ 2*((z*) N p i)^2:=by
    obtain ⟨-, -, -, hv,h'⟩:=H.seed.wilson.represents N p i hi
    have hh:= zero_lt_one.trans (C.path.levels.fits.delayed i); have hz:= Real.sqrt_pos.mpr ((by linarith only [hh] : 0 < gB i/2).trans_le hv)
    unfold Pert.Asymptotics.regulatorRun; refine ⟨inv_pos.mpr hz,?_⟩; field_simp
    rw [Real.sq_sqrt ((by linarith only [hh] : 0 ≤ gB i/2).trans hv)]; linarith only [h']
/-- Same payment for every fixed product horizon tuple/layout aspect and desired perturbative order.
Only ANNULAR noncolliding banks in the native range with paid label norms. -/
theorem product_bank (H₀:Citizen C W r D)(d : J→ℕ) (hE:0<E) (t u e:ℕ) : ∀ᶠ k:ℕ in atTop,∀ (n:ℕ), (C.path.levels.budget k).B^8 ≤ n → (n:ℝ) ≤ (C.path.levels.clock.hatBeta k)^e → ∀ N p (h:k<N)(x:J→Site (C.side k p)), Rooms C k p n E x→ ∀ q:(j:J)→C.label (d j), (∀ j, Spindle.paid C (d j) k N p (q j) ≤ gB k^t) →
    ‖unmaskedT C N k p h.le x q - nominal C N k p x q‖ ≤ Pert.Asymptotics.regulatorRun C N p k^(2*u):=by
   let K:ℕ×ℕ→ℕ:= Prod.fst; let n:ℕ×ℕ→ℕ:= Prod.snd; let S:=(Filter.comap K atTop); let A : Set (ℕ×ℕ):={q | (B#) (K q)^8≤ n q ∧ (n q:ℝ)≤ gB (K q)^e}; let M:= S ⊓ Filter.principal A
   let v:ℕ×ℕ→ℝ:= fun i=> gB (K i)^t; let prices (i:ℕ×ℕ):=((gB (K i))⁻¹)^u/(2^u)
   have h:Tendsto K M atTop:= tendsto_iff_comap.mpr inf_le_left; have hB:∀ᶠ i in M,i∈A:= Filter.Eventually.filter_mono (show M ≤ (Filter.principal A) from inf_le_right) ((eventually_principal).mpr (fun _ h=>h))
   have hw:Height C.S M (C.S.scale ∘ K) K 1:= ⟨h,tendsto_const_nhds.congr' (((C.S.divergent.comp h).eventually_gt_atTop 0).mono fun i hi=>(div_self («a»:=C.S.scale (K i)) (ne_of_gt hi)).symm)⟩; have hz:= C.S.divergent.comp h; have hp:= hat_price hz hw; have hk:Coins M (C.S.scale ∘ K) v:= Coins.power hp hz _; have hv(i):1 ≤ gB (K i):= (C.path.levels.fits.delayed _).le
   have hS:Coins M (C.S.scale ∘ K) prices:= Coins.div (Coins.power (Coins.inv hp) hz _) (Bi.const _ (show (2:ℝ)^u≠0 from by positivity) hz)
   have hx:= paid_many (d:=d) H (show GracesP C M K n from ⟨h,(Cheap.power hp.up hz e).norm_le (hB.mono fun i (hi:i∈A)=> (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _))),hB.mono fun i (hi:i∈A)=> hi.1⟩) H₀ hE hk (Eventually.of_forall (fun i=>one_le_pow₀ (hv i))) hS (Eventually.of_forall (fun i=>(div_pos (pow_pos (inv_pos.mpr (zero_lt_one.trans_le (hv i))) _) (pow_pos (by norm_num) u) : 0< prices i))); rw [Filter.eventually_inf_principal] at hx
   obtain ⟨u',hu,hU⟩:= hx; filter_upwards [hu] with i hi b he hx N p h x hv q hz
   refine (hU (show (i,b)∈ K ⁻¹' u' from hi) ⟨he,hx⟩ N p h x hv q hz).trans ?_; unfold prices
   have hv': 0 < gB (K (i,b)):= zero_lt_one.trans_le (C.path.levels.fits.delayed _).le
   refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (inv_pos.mpr hv').le (bandRun H (p:=p) h.le).2 u) (pow_nonneg zero_le_two _)).trans_eq ?_; rw [mul_pow, pow_mul]; field_simp

omit H
theorem common (G:Gauge)(h:G.Simple)(b:ℝ)(hb:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Wcmain C ∧ (∀ f:Extraction.Order, ∃ g:Extraction.Order,∃ S:Table C.book, OPE.Services C (f.refine g) S ∧ ∃ (F:Spec.Final C (f.refine g) S) (L:EveryPhase.Almanac F), EveryPhase.Completed F L) ∧
     ∀ (E u v t:ℕ) {J:Type} [Fintype J] [DecidableEq J](d:J→ℕ), 0<E → ∀ᶠ k:ℕ in atTop,∀ n:ℕ, (C.path.levels.budget k).B^8 ≤ n → (n:ℝ)≤ C.path.levels.clock.hatBeta k^t → ∀ N p (h:k<N)(x:J→Site (C.side k p)), Rooms C k p n E x→ ∀ q:(j:J)→C.label (d j), (∀ j, Spindle.paid C (d j) k N p (q j) ≤ C.path.levels.clock.hatBeta k^v) →
    ‖unmaskedT C N k p h.le x q-nominal C N k p x q‖ ≤ Pert.Asymptotics.regulatorRun C N p k^(2*u):= by
    obtain ⟨C',hB,hC,hM,hW,⟨W',r,D,hS⟩,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.lucent_supplied h hb
    obtain ⟨σ',γ',h'⟩:=Yarn.enroll hS.toSharper hM h
    refine ⟨C',hB,hC,hM,hW,?_,fun E u v t J i₁ i₂ d hE=>product_bank (H:=h') hS d hE v u t⟩ -- fix
    intro f
    obtain ⟨g,A,L,R,T,E0,hA,x,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) x.copies
    obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E0) H h hs hG x hA.clean.ready hA.clean.tilt
    obtain ⟨F⟩:=Acme.glistens hC hA.clean.ready hA.clean.tilt p; refine ⟨g,T,⟨hs,h,⟨W',r,D,hS.toPackage⟩,A,L,R,E0,hA⟩,F,EveryPhase.all_characters F⟩
end YM.GapsR2RG
