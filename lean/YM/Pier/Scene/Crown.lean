import YM.Pier.Scene.Symbols
/-! Earned estimate for replacing measured moment by its actual scene estimate
on enamel. Supports arbitrary finite arity (including trivial), native
separations, and each finite price demand along a measured GracesP. Does not
price perturbative diagrams. Note unprojected support of each label tracked
through the entire *actual* scene. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe.Panoramic
open Pier.Scene Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
variable {φ:Filter I}{u ℓ:I→ℕ} {v s:I→ℝ}
  (L: GracesP C φ u ℓ) (T₀:Citizen C W r D) {wide:ℕ} (hbig:1≤wide)
variable (hv : Coins φ (C.S.scale ∘ u) v)(hp : ∀ᶠ i in φ,1≤v i)
    (hs : Coins φ (C.S.scale ∘ u) s)(ht : ∀ᶠ i in φ,0<s i)
    (d:J→ℕ)
set_option quotPrecheck false
local notation "B" i=> ((C.path.levels.budget (u i)).B)
local notation "t*" => Fintype.card J
open GridApprox

include H T₀ hbig L hv hp hs ht
omit [Fintype J] in
private lemma spacePaid (Q:Finset J)(g:J→Bool) (h : ∃ i ∈ Q, g i=true) :
    ∀ᶠ i in φ, ∀ N p,∀ he:u i < N,∀ x:J→Site (C.side (u i) p), (∀ k j,separation (x k) (x j) ≤ wide*ℓ i) → (∀ k j,k≠j → ℓ i≤ separation (x k) (x j)) → ∀ x₁:(j:J)→ C.label (d j), (∀ j, Spindle.paid C (d j) (u i) N p (x₁ j) ≤ v i) → ‖moment (C.beta N p) (fineJob (fun j=> writeF C (x₁ j) N (u i) p ((C.path.levels.budget (u i)).B) (x j) he.le (g j)) Q)‖ ≤ s i:= by
  obtain ⟨i₀,hm,h⟩ := h
  filter_upwards [neighbors H L T₀ wide hbig (fun i:Q=> d i.val) (fun i=>g i.val) ⟨⟨i₀,hm⟩,h⟩ hv (hp.mono fun _ hi=> zero_lt_one.trans_le hi) hs ht] with i h n p he x hX hD x₁ hv
  let F (j:J) := writeF C (x₁ j) n (u i) p (B i) (x j) he.le (g j)
  have hv:= h n p he (x ∘ Subtype.val) (fun a b=> hX ..) (fun a b h=> hD _ _ fun h'=> h (Subtype.ext h')) (fun j=> x₁ j.val) (fun j=>hv _)
  change ‖moment (C.beta n p) (fineJob F Q)‖ ≤ _
  rw [show fineJob F Q= fineJob (fun a:Q=>F a.val) univ from funext (fun x=> Finset.prod_subtype _ (p:=fun x=> x∈Q) (fun _=>Iff.rfl) (fun j=>F j x))]; exact hv

private lemma allMany :
    ∀ᶠ i in φ, ∀ N p,∀ he:u i < N,∀ x:J→Site (C.side (u i) p), (∀ k j,separation (x k) (x j) ≤ wide*ℓ i) → (∀ k j,k≠j → ℓ i≤ separation (x k) (x j)) → ∀ x₁:(j:J)→ C.label (d j), (∀ j, Spindle.paid C (d j) (u i) N p (x₁ j) ≤ v i) → ∀ s':Finset J, ‖moment (C.beta N p) (fineJob (fun j=>abrade C (x₁ j) N (u i) p (x j) he.le) s') - moment (C.beta N p) (fineJob (fun j=>GridApprox.backTo C.path N p he.le (bead C (d j) (u i) N p (B i) (x₁ j) (x j))) s')‖ ≤ s i :=by
  let z:ℝ:=2^t* *2^t*; let c i:= s i/(z * ((v i)^t*)); have hν:0<z:= by unfold z; positivity
  have hT:= C.S.divergent.comp L.seeks
  have hc : Coins φ (C.S.scale ∘ u) c:= Coins.div hs (Coins.mul (Bi.const z hν.ne' hT) (Coins.power hv hT t*))
  have hP : ∀ᶠ i in φ,0<c i:= (ht.and hp).mono fun i hi=> div_pos hi.1 (mul_pos hν (pow_pos (zero_lt_one.trans_le hi.2) _))
  -- use on every admissible pair of subset + split
  let S':Type:= {t: Finset J × (J→Bool) // ∃ i∈t.1,t.2 i=true}
  letI: Fintype S' := by dsimp [S']; infer_instance
  filter_upwards [eventually_all.mpr (fun Q:S'=>spacePaid H L T₀ hbig hv hp hc hP d Q.val.1 Q.val.2 Q.property),
    hp,hP,eventually_all.mpr (fun j=> L.seeks.eventually_ge_atTop (C.ref (d j)))] with i h hv hc hA N p he x hX hD x₁ hB s'
  let e(j:J):= cameo C (d j) (u i) N p (x₁ j)
  let g(j:J)(b:Bool):=writeF C (x₁ j) N (u i) p (B i) (x j) he.le b
  let X(j):=abrade C (x₁ j) N (u i) p (x j) he.le; let Y(j:J):= GridApprox.backTo C.path N p he.le (bead C (d j) (u i) N p (B i) (x₁ j) (x j))
  have hF(j:J): g j false=X j-(fun _=>e j):=by unfold g; rw [erased _ _ _ he.le]; exact if_neg (by decide)
  have hG(j:J): g j true=X j-Y j:=by unfold g; rw [erased _ _ _ he.le]; exact if_pos rfl
  have hH (j y): X j y=g j false y + e j := by rw [hF,Pi.sub_apply]; exact (sub_add_cancel ..).symm
  have hB'(j y): Y j y=X j y - g j true y:= by rw [hG,Pi.sub_apply]; exact (sub_sub_cancel ..).symm
  refine (payMany s' e (fun j b=> write_e H (x₁ j) _ _ he.le (hA j) b) hH hB' hc.le
    (fun t _ g h' => h ⟨(t,g),h'⟩ N p he x hX hD x₁ hB) (fun j=> cameo_price _ (hB j)) hv).trans_eq ?_
  have hv : 0 < v i:= zero_lt_one.trans_le hv; unfold c z; field_simp

-- Need common interior window and then orientation for backs_many, purchases attained before any subset.
-- Include vacant I (e.g. perturbation tag quiet).
lemma overBoard : ∀ᶠ i in φ, ∀ N p,∀ he:u i < N,∀ x:J→Site (C.side (u i) p), (∀ k j,separation (x k) (x j) ≤ wide*ℓ i) → (∀ k j,k≠j → ℓ i≤ separation (x k) (x j)) → ∀ x₁:(j:J)→ C.label (d j), (∀ j, Spindle.paid C (d j) (u i) N p (x₁ j) ≤ v i) → ∀ s':Finset J, ‖moment (C.beta N p) (fineJob (fun j=>abrade C (x₁ j) N (u i) p (x j) he.le) s') - ∫ U, fineJob (fun j=> bead C (d j) (u i) N p (B i) (x₁ j) (x j)) s' U ∂(Therm.scene C.path N p (u i))‖ ≤ s i :=by
    rcases isEmpty_or_nonempty J with hJ|hJ
    · filter_upwards [ht] with i hi N p he x hX hz v hV s'
      letI:= hJ; letI:= Therm.probability (p:=p) H.seed.wilson he.le
      rw [Subsingleton.elim s' (∅:Finset J)]; simpa [fineJob,moment] using hi.le
    letI:=hJ; obtain ⟨mx,hx,hM⟩:= Finset.exists_max_image univ (fun j=> BasisCost.extent (C.localSection (d j))) Finset.univ_nonempty
    obtain ⟨z,hz,hzm⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 (Fintype.card J))).exists
    filter_upwards [allMany H L T₀ hbig hv hp hs ht d, bolted H L T₀ (d mx) 0 hzm hz,eventually_all.mpr fun j=>L.seeks.eventually_ge_atTop (C.ref (d j))] with i h hX he N p hN x hr hq z hz s'
    let F(j):= bead C (d j) (u i) N p (B i) (z j) (x j)
    let q:= omen C (d mx) (u i) (B i)
    let f:= fineJob F s'
    have hv(j:J): Interior (GridApprox.window (x j) q) (F j) := (bead_local H (x j) (z j) (he j) hN.le (B i)).enlarges (fun y h=> sparrow.mpr ((sparrow.mp h).trans (Nat.add_le_add_right (hM j (mem_univ _)) _)))
    have ht:= (backs_many C.path q N p _ N x s' hv (fun i j h=> hX.gain.trans_le (hX.paid.trans (hq i j h))) hN.le)
    let u₁(j):= backTo C.path N p hN.le (F j); let Y:= fineJob u₁ s'
    have he : Envelope f:= Envelope.prodC s' F (fun j _=> cylinder_env (hv j))
    have hF : (∫ U,f U ∂(Therm.scene C.path N p (u i)))= moment (C.beta N p) Y := by
       rw [← Therm.retro (k:=u i) H.seed.wilson hN.le le_rfl f he]; have hV:= backTo_env C.path N p hN.le he; exact (Therm.onstage H.seed.wilson _ (hV.integrableC _)).trans (congr_arg (moment _) ht)
    rw [hF]; exact h _ _ hN x hr hq z hz s'
end YM.OPE.Strobe.Panoramic
