import YM.WilsonBridge.Master

/-!
# Complete coefficient-level resolution identity with ∆ and marked BV

This uses the bare perturbative variable of the Wilson rule, extracting rank minus two
on the action, rank on Haar, rank minus an arbitrary stipulated external coupling
power on an insertion. Unlike cover Ward identities tested by momentum germs, this
will be checked *exactly* on a finite based-gauge alphabet. Total vacuum and insertion
ranks are kept separately. Still at a single finite mesh.
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit MS.Book.Convolve
open Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Orbit.LogReal Orbit.Cog
open Function Finset
open scoped BigOperators
variable {V I : Type} {p : Sector V} [Fintype V] [Fintype I]
variable {B : Bonded p I} {W H O F G : Raw V ℂ}
local notation "Δ" => B.BV (R:=ℂ)
namespace FreeBV
local notation "M" => PermV p
local infixl:70 " ⋆ " => Actors.core M
local notation "⟦" X "," Y "⟧" => FreeBV.crossBV B X Y
local notation "[" X ";" Y "]s" => link Δ true p X Y
local notation "pr" => promote Δ
local notation "δ" => useN.refineV
local notation "fullL" => tokM B
variable (Z:FreeBV B)
local notation "DΩ" => Z.total
local notation "SΩ" => δ Z.quadratic

/-- Specification of the exact finite exponent *before* the free gauge fixing:
coordinate rank Taylor tensors of the action incl orbit ghosts, and Haar log.
The equations here use canonical Laplacian in independent orbit coordinates. -/
structure MasterLaw (B:Bonded p I) (W H : Raw V ℂ) : Prop where
    smoothW : MS.Koszul.Symm p W
    smoothH : MS.Koszul.Symm p H
    evenW : Pure p false W
    evenH : Pure p false H
    start : From W 2
    haar_normalized : H []=0
    classicalWard : link B.BV true p W W=0
    determinant : B.BV W+link B.BV true p W H=0
    flatDet : B.BV H=0
    detCentral : link B.BV true p H H=0

omit [Fintype V] in
lemma link_ranked {d e:ℤ} (h:From F d) (g:From G e) :
    ⟦rankLevel d F,rankLevel e G⟧ = rankLevel (d+e-2) [F;G]s := funext fun k=> link_level B k h g -- F auto?
omit [Fintype V] [Fintype I] in
lemma rank_zero_series (d:ℤ) : rankLevel d (0:Raw V ℂ)=0:=funext fun _=>map_zero _
omit [Fintype V] in
lemma lap_ranked {d:ℤ} : pr (rankLevel d F) = rankLevel (d-2) (Δ F):=funext fun k=>lap_level B k
omit [Fintype V] [Fintype I] in
lemma basis_level {d:ℤ} (hv : MS.Koszul.Symm p G) : Γ (rankLevel d G) p :=
  fun _ _=> ⟨mask_symm hv,minH (Limit.mod _ _)⟩
omit [Fintype V] [Fintype I] in
lemma even_level {d:ℤ} (hv : Pure p false G) : rankLevel d G∈(M).guard :=
  fun _ _=> mask_pure hv

local notation "WΞ" => rankLevel 2 W
local notation "HΞ" => rankLevel 0 H

def relative (F : T (Raw V ℂ)): T (Raw V ℂ) := F - δ (F 0)
def action (W H : Raw V ℂ) : T (Raw V ℂ):= rankLevel 2 W+ rankLevel 0 H
abbrev interaction (W H : Raw V ℂ) := relative (action W H)

namespace MasterLaw
variable (h:MasterLaw B W H)
include h
omit [Fintype V] in
lemma at_origin : action W H 0=mask 2 W := by
    have he : mask 0 H=coin 0:= by
        have hh:=rank_zero_eq_coin (rankMod H 0)
        rw [enough (F:=H) [] (h:=0) rfl,h.haar_normalized] at hh; exact hh
    have hv : (coin (0:ℂ) : Raw V ℂ)=0:= funext fun a=> by cases a<;> rfl
    change mask 2 W+ mask 0 H= _
    norm_num [he,hv]

omit [Fintype V] in
lemma quadratic_master : link Δ true p (mask 2 W) (mask 2 W)=0 := by
    have hp:= congr_fun (link_ranked (B:=B) h.start h.start) 0
    rw [h.classicalWard,rank_zero_series] at hp
    change (∑ x∈antidiagonal (0:ℕ), [WΞ x.1; WΞ x.2]s)=0 at hp
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at hp
    exact hp
omit [Fintype V] in
lemma charge : fullL (action W H)=0:= by
    have hh : From H 0:= fun _ hi=> by omega
    have he: rankLevel (2-2) (Δ W) + rankLevel (2+0-2) ([W;H]s)=0 := by
        funext k; change mask (k+0:ℤ) (Δ W) + mask (k+0:ℤ) [W;H]s=0; rw [←map_add,h.determinant,map_zero]
    change pr (WΞ+HΞ)+ (1/2:ℂ) • pairW (tokenL Δ true p) (WΞ+HΞ) (WΞ+HΞ)=0
    rw [← cross_promote]; simp_rw [map_add,LinearMap.add_apply]
    rw [cross_central (even_level h.evenH) (even_level h.evenW),link_ranked h.start h.start,link_ranked hh hh,link_ranked h.start hh, lap_ranked,lap_ranked,h.classicalWard,h.flatDet,h.detCentral]; simp_rw [rank_zero_series]; linear_combination (norm:=module) he

omit [Fintype V] [Fintype I] h in
lemma initial_zero : interaction W H 0=0:= by simp only [interaction,relative, Pi.sub_apply, lone_use, sub_self]
omit [Fintype V] in
lemma even_interaction : interaction W H∈(M).guard:= by
    have hv : action W H∈(M).guard := (M).guard.add_mem (even_level h.evenW) (even_level h.evenH)
    exact (M).guard.sub_mem hv (refineπ useN _ (hv 0 (Set.mem_univ _)))
omit [Fintype V] in
lemma supported : Γ (interaction W H) p := by
    have hv : Γ (action W H) p := (allIndex (FeeP p) ℕ).add_mem (basis_level h.smoothW) (basis_level h.smoothH)
    exact (allIndex (FeeP p) ℕ).sub_mem hv (refineπ useN _ (hv 0 (Set.mem_univ _)))
end MasterLaw

lemma lift_link (F : T (Raw V ℂ)): ⟦SΩ,F⟧= promote Z.Q.deriv F:= by
    unfold crossBV; rw [useN.tile]; exact funext fun i=> (Z.hamiltonian (F i)).symm
variable {Z}
lemma recenter {X : T (Raw V ℂ)} (hx : X∈(M).guard) (he:X 0= Z.quadratic) :
    DΩ (relative X) + (2:ℂ)⁻¹ • ⟦relative X,relative X⟧ = fullL X := by
  let V' := relative X
  have hv : V' ∈ (M).guard:= (M).guard.sub_mem hx (refineπ useN _ (hx 0 (Set.mem_univ _)))
  have hq : SΩ ∈ (M).guard:= refineπ useN _ Z.even
  have ha : X=SΩ+V':= by unfold V' relative; rw [he]; abel
  have hb : ∀ (T': T (Raw V ℂ)), DΩ T'= promote Z.Q.deriv T'+ pr T':= fun _=> rfl
  have hl : pr SΩ=0:= by funext i; unfold SplitP.refineV; rw [promised]; split; exact Z.div; exact map_zero _
  have hp : ⟦SΩ,SΩ⟧=0:= by
    rw [Z.lift_link]; funext i; unfold SplitP.refineV; rw [promised]; split; exact (Z.hamiltonian _).trans Z.classicalMaster; exact map_zero _
  unfold tokM; rw [←cross_promote]; change DΩ V'+_ • ⟦V',V'⟧ = _
  rw [ha]; simp_rw [map_add,LinearMap.add_apply]; rw [hl,hp,cross_central hv hq,hb,Z.lift_link]; norm_num; module

/-- This covers a joint product too (it may be presented as one marked stencil).
    Explicit coupling power stripped before perturbative coefficients: `O` should have
    rank at least the number to be stripped. -/
structure PhysicalLaw (B:Bonded p I) (W H : Raw V ℂ) (O : Raw V ℂ) (d : ℤ) : Prop where
    symm : MS.Koszul.Symm p O
    even : Pure p false O
    starts : From O d
    ghost_free_lap : B.BV O=0
    gauge : link B.BV true p W O=0
    ghost_free_haar : link B.BV true p H O=0

namespace MasterLaw
variable (h:MasterLaw B W H)
include h
lemma complete (he : WΞ 0 = Z.quadratic) : DΩ (exp0 p (interaction W H))=0:=
  Z.annihilates h.even_interaction (initial_zero) ((recenter (X:=action W H) ((M).guard.add_mem (even_level h.evenW) (even_level h.evenH)) (h.at_origin.trans he)).trans h.charge)
lemma inserted {d:ℤ} (hu : PhysicalLaw B W H O d) (he : WΞ 0 = Z.quadratic) :
    DΩ (exp0 p (interaction W H) ⋆ rankLevel d O)=0 := by
    have hz:= h.at_origin.trans he
    have hH : From H 0:=fun _ hx=>by omega
    apply Z.closed_series h.even_interaction initial_zero ((recenter ((M).guard.add_mem (even_level h.evenW) (even_level h.evenH) : action W H∈(M).guard) hz).trans h.charge)
    rw [show DΩ (rankLevel d O)= promote Z.Q.deriv (rankLevel d O)+ pr (rankLevel d O) from rfl, ← Z.lift_link]
    unfold interaction relative; rw [hz,map_sub,LinearMap.sub_apply, action,map_add,LinearMap.add_apply,link_ranked h.start hu.starts,link_ranked hH hu.starts,lap_ranked,hu.gauge,hu.ghost_free_haar,hu.ghost_free_lap]; simp_rw [rank_zero_series]; abel
end MasterLaw
end FreeBV

namespace Based
open Kinetics Kinetics.Fixing FreeBV
variable {J:Type}[Fintype J] [DecidableEq I] [DecidableEq J] {T:Kinetics J I}
    {W H O : Raw (Letters J I) ℂ}
variable (h:T.Blocks (mask 2 W))(hw:MasterLaw (bracket J I) W H)(P P' : Fixing T)
include h hw
local notation "τφ" => parity J I
local notation "M" => PermV τφ
local notation "Q" => interaction W H
local notation "X" => exp0 τφ Q
local infixl:70 " ⋆ " => Actors.core M

lemma vacuum_independent : ℶV P.half X=ℶV P'.half X := by
    let Z:= h.toFreeBV (rankMod W 2) (mask_symm hw.smoothW) (mask_pure hw.evenW) hw.quadratic_master
    have hr : rankLevel 2 W 0=Z.quadratic:=rfl
    funext i
    have he:= fee_spec (expΓ hw.supported i (Set.mem_univ _))
    exact P.wick_independent he.2 he.1 h Z.rank (mask_symm hw.smoothW) (mask_pure hw.evenW) hw.quadratic_master P' (congr_fun (hw.complete hr) i)
lemma marked_independent {d:ℤ} (ho:PhysicalLaw (bracket J I) W H O d) :
    ℶV P.half (X ⋆ rankLevel d O)=ℶV P'.half (X ⋆ rankLevel d O) := by
    let Z:= h.toFreeBV (rankMod W 2) (mask_symm hw.smoothW) (mask_pure hw.evenW) hw.quadratic_master
    have hr : rankLevel 2 W 0=Z.quadratic:=rfl
    funext i
    have he:= fee_spec (ΤΓ_pair (expΓ hw.supported) (basis_level (d:=d) ho.symm) i (Set.mem_univ _))
    exact P.wick_independent he.2 he.1 h Z.rank (mask_symm hw.smoothW) (mask_pure hw.evenW) hw.quadratic_master P' (congr_fun (hw.inserted ho hr) i)
lemma gauge_change {d:ℤ} (ho:PhysicalLaw (bracket J I) W H O d) (Z:ℕ→ℂ) :
    Endμ P.half τφ Q (rankLevel d O) Z ↔ Endμ P'.half τφ Q (rankLevel d O) Z := by
    unfold Endμ; rw [vacuum_independent h hw P P', marked_independent h hw P P' ho]
end Based
end YM.WilsonBridge
