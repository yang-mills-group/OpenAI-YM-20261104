import YM.RG05Readout.Petals.Refrain
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Chalice
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Petals Petals.Kernel Bay Dash
/-!
# MANY-slot projection surcharges, separated supports. This pays before dividing by full UV path and OPE.
 We are granted Budget from EACH actual vetted stroke in its own dimension (may give different disappearing rate). Emits estimate on *actual joint normalized Wilson moments* to replace all of them by snapshot Horizon projected rows simultaneously, even among still stencil-growing words, arbitrary derivative demand of those same probes.Finiteness constants depend n, no perfect Ward scope assumed at diagonal. -/
open UVExt UVExt.Slots
variable {f:Extraction.Order} {α:Fin n → Trial C} {r:Rowe C d} {s:ℝ}
lemma updates (i:Fin n)(t:ℕ×ℕ→ℂ)(a:Fin n→ Trial C) (z:Fin n→Site (C.side N p)) (P:Trial C): UVExt.Slots.probes N p n (Function.update a i (Kernel.times t P)) z=t (N,p) * UVExt.Slots.probes N p n (Function.update a i P) z:=by
   simp_rw [probes_update]; unfold moment; unfold Kernel.times; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc];exact integral_const_mul ..
section
variable (K:CenterPort C f) (D: Fin n→Trial C) (i:Fin n) 
local notation "Z"=> C.side N p
local notation "x!"=> Fin n→Site (C.side N p)
include h
lemma erase_one {P Q:Trial C}(hF:Reveals C f P r)(hx:Q=Bid.upper C r)(hs:∀ j,Stencilled f (D j))(hw:∀ j,isolated f (D j))(hv:0<s) : ∃ b:Cutoffs→ℝ,(∀ i,0≤ b i) ∧ Tendsto b f.fuse (𝓝 0)∧ f.late fun N p=>∀ x:Fin n→ Site (C.side N p), (∀ i j,i ≠ j → s ≤ C.S.a N * separation (x i) (x j)) → ‖UVExt.Slots.probes N p n (Function.update D i P) x - UVExt.Slots.probes N p n (Function.update D i Q) x‖ ≤ b (N,p):=by
    obtain ⟨hP,hR,z,hz,ht,he⟩:= hF; subst Q; let q:= Bid.upper C r; let v:= P-z-q
    have hQ : Stencilled f q:= Stencilled.upper h r; obtain ⟨b,hb,hB,X,hX,h₁,h₂⟩:= faded h ((hP.sub ht).sub hQ) he
    have hG: isolated f X:= ⟨0, manifest_zero C,⟨∅, Eventually.of_forall fun i=> ⟨fun _ _=>rfl,fun x=> Interior.constant _ _⟩⟩,sub_zero X|>.symm ▸ h₂⟩
    have hM(j): Stencilled f (Function.update D i X j):=by by_cases hx:i=j;subst j; rwa [Function.update_self]; rw [Function.update_of_ne (Ne.symm hx)]; exact hs j
    have hΓ(j): isolated f (Function.update D i X j):=by by_cases hx:i=j;subst j; rwa [Function.update_self];rw [Function.update_of_ne (Ne.symm hx)]; exact hw _
    obtain ⟨A,hA,hH⟩:= erased_bounds h _ hM hΓ hv
    have hs'(j): Stencilled f (Function.update D i z j):=by by_cases hx:i=j; subst j; rwa [Function.update_self]; rw [Function.update_of_ne (Ne.symm hx)];exact hs j
    have ht':= erase_manifest h (Function.update D i z) hs' i (by rw [Function.update_self]; exact hz) hv
    have h'u := hB.mul_const A; rw [zero_mul] at h'u; refine ⟨_,fun i=>mul_nonneg (hb i|>.le) hA,h'u,?_⟩
    have h₃:= probes_minus i hs hP ht; have h₄:= probes_minus i hs (hP.sub ht) hQ
    filter_upwards [hH,h₃,h₄,ht'] with p h hp hL hT; filter_upwards [h,hp,hL,hT] with N hx hv hβ he x hu
    rw [← (show UVExt.Slots.probes (f.mesh N) (f.per p) n (Function.update D i (P-z)) x=UVExt.Slots.probes (f.mesh N) (f.per p) n (Function.update D i P) x from (hv x).trans (by rw [he x (fun j hj=> hu _ _ hj),sub_zero])), ←hβ]
    rw [hX,updates ..,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hb _).le]; exact mul_le_mul_of_nonneg_left (hx _ hu) (hb _).le
include K
lemma isolated_visit {P:Trial C}(H:Reveals C f P r) : isolated f P ∧ isolated f (Bid.upper C r):=by
   obtain ⟨hs,hU,z,hz,hP,hR⟩:=H; let v:=Bid.upper C r; have hp:TiledCaps C f v:= from_tight h K hU
   exact ⟨⟨z,hz,hP,(sub_add_cancel (P-z) v ▸ ((from_close h hR).add h hp))⟩, 0,manifest_zero C, ⟨∅,Eventually.of_forall fun i=> ⟨fun _ _=>rfl,fun x=>Interior.constant _ _⟩⟩,sub_zero v|>.symm ▸ hp⟩ -- hp transport simp
-- sample READ discrepancy
lemma discrepancy {g:Fin n→ℕ}{v:(i:Fin n)→Rowe C (g i)}(hp:∀ i, Reveals C f (D i) (v i)) (hσ:0<s): ∃ b:Cutoffs→ℝ,(∀ i,0≤ b i) ∧ Tendsto b f.fuse (𝓝 0) ∧ f.late fun N p=> ∀ x:Fin n→Site (C.side N p), (∀ i j,i ≠ j → s ≤ C.S.a N * separation (x i) (x j)) →
     ‖UVExt.Slots.probes N p n D x- UVExt.Slots.probes N p n (fun i=>Bid.upper C (v i)) x‖ ≤ b (N,p):=by
    let F (J : Finset (Fin n)) (i:Fin n):= if i ∈ J then Bid.upper C (v i) else D i
    suffices hv: ∀ J: Finset (Fin n), ∃ b:Cutoffs→ℝ,(∀ i,0≤ b i) ∧ Tendsto b f.fuse (𝓝 0) ∧ f.late fun N p=> ∀ x:Fin n→Site (C.side N p), (∀ i j,i ≠ j → s ≤ C.S.a N * separation (x i) (x j)) →
       ‖UVExt.Slots.probes N p n D x- UVExt.Slots.probes N p n (F J) x‖ ≤ b (N,p) by simpa only [F,Finset.mem_univ,if_true] using hv Finset.univ
    have hS (J i) : Stencilled f (F J i):=by unfold F;split;exact Stencilled.upper h _;exact (hp i).1
    have hL (J i) : isolated f (F J i):=by unfold F;split;exact (isolated_visit h K (hp i)).2; exact (isolated_visit h K (hp i)).1
    intro J; induction J using Finset.induction_on with
    | empty=> refine ⟨0,fun _=>le_rfl,tendsto_const_nhds,Eventually.of_forall fun i=>Eventually.of_forall fun j x _=> by simp [F]⟩
    | insert i J hi ih=>
       have hT:= erase_one h (F J) i (hp i) rfl (hS J) (hL J) hσ; obtain ⟨b,hb,hB,hV⟩:=ih; obtain ⟨c,hc,hC,hQ⟩:=hT
       rw [show Function.update (F J) i (D i)=F J from funext fun j=> by by_cases h':j=i;subst j; simp [F,hi]; rw [Function.update_of_ne h'],show Function.update (F J) i (Bid.upper C (v i))=F (insert i J) from funext (fun j=>by by_cases h':j=i; subst j;simp [F]; simp [F,h'])] at hQ
       have hx:= hB.add hC; rw [zero_add] at hx; refine ⟨_,fun i=>add_nonneg (hb i) (hc i),hx,?_⟩
       filter_upwards [hV,hQ] with P hv hh; filter_upwards [hv,hh] with N he ht x hX; let W(q):= UVExt.Slots.probes (f.mesh N) (f.per P) n q x
       change ‖W D-W _‖≤ _; rw [show W D-W (F (insert i J))=(W D-W (F J))+(W (F J)-W (F (insert i J))) from (sub_add_sub_cancel ..).symm]; exact (norm_add_le ..).trans (add_le_add (he x hX) (ht x hX))
end
end YM.RG05Readout.Chalice
