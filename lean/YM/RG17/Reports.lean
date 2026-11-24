import YM.RG17.Recover

/-!
# From marked-capture reports in full field letters (pending)

to quantitative numerical separated correlation and OPE
matching, in the measured pivot frames. These reduce target `qfull`
(in this reporting version, not arbitrary scheme comparisons).
Specific arities/horizons/order may request less than `Sends` below.
See Docs (`checks/RG17`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S} {L:Layout F} (Z:Ledger L)
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S) {n:ℕ}{d:Fin n→ℕ}
set_option quotPrecheck false
local notation "ρ"=>OPE.run

structure Terminal (Z:Ledger L) (A:Ports C) (v:(i:Fin n)→ Slot C (d i))(D:ℕ)(K:Set (Points n))(p:ℕ) : Prop where
    tail : ∀ j≤p,Cost Z (jointTests K) 0 (A.ope v D j)
    faces (q:ℕ) (hq:q ≤ p) : Cost Z (jointTests K) (q+1)
      (fun r ψ=> forecast Z q (combine (A.read D) (A.marked v D)) r ψ - forecast Z q (A.ope v D) r ψ)

variable (A:Ports C){p:ℕ}(loc:Located L) {v:(i:Fin n)→ Slot C (d i)} {K:Set (Points n)}
include loc H
lemma opeReport {D:ℕ}(hx:IsCompact K)(he:K⊆ conf n) (hr:Returns Z A v D K p) (ht:Terminal Z A v D K p) {W b₀} (hk:Diagnostics (D:=D) A Z W b₀ p)(hz:ProbesAt A Z W p)
    {q:ℕ}(hq:q≤p): Cost Z (jointTests K) (q+1) (fun r ψ=> toFrame L D r (basket P D (stems L v r) r ψ)-forecast Z q (A.ope v D) r ψ):=by
   obtain ⟨X,hX⟩:=spatialLocated P L H loc v D hx he
   obtain ⟨u,hu,hc,M,hM,h⟩:= hr.simultaneous X
   obtain ⟨b,c,k,hb,hc',hX⟩:= hX M hM
   let R r:=‖toFrame L D r‖
   let w (r:ℝ)(a:Test n):=master L D r (M a r)
   let V (r:ℝ)(a:Test n):=basket P D (stems L v r) r a
   have hY:Cost Z (jointTests K) (q+1) (fun r a=> toFrame L D r (V r a - w r a)):=by
       let F'(r:ℝ):= R r * (c*r^((D:ℝ)+b))
       have hx:RateLE home ρ F' (-b):=by
           have hp:RateLE home ρ R D:= (frameBound Z P H loc hk hz).transfer (G:=R) (Eventually.of_forall fun i=> (norm_norm (toFrame L D i)).le)
           have ht:= hp.mul ((RateLE.const c ageLarge).mul ((lengthRate.rpow ((D:ℝ)+b)).pays ageLarge)); rw [show (D:ℝ)+(0+(D+b)*(-1))=-b by ring] at ht; exact ht
       apply Cost.coarse (neg_lt_zero.mpr hb) _ F' hx k
       filter_upwards [hX] with r hM ψ a ha
       exact ((toFrame L D r).le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hM _ ha.1 a ha.2) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)
   have hV:= Cost.payAt (fun i hi=> hc i ((hi.trans hq).trans hu.le)) (fun i hi=> hk.readPrice i (hi.trans hq)) (Cost.openTerm (lt_of_le_of_lt hq hu) (fun i _ hi=>hc i hi) h) (columnBill Z P H loc hk hz hq)
   refine ((hY.add hV).add (ht.faces _ hq)).congr (Eventually.of_forall fun r ψ=>?_)
   rw [map_sub]; change _-_+(toFrame L D r (w r ψ)-_)+_=toFrame L D r (V r ψ)-_; abel

structure Sends (Z:Ledger L)(A:Ports C)(p:ℕ) : Prop where
   -- Pointwise premise schemas. Constant depends on all finite dimensions and profile family.
   mission : ∀ (n:ℕ) (d:Fin n→ℕ) (v:(i:Fin n)→ Slot C (d i)) (K:Set (Points n)), IsCompact K → K⊆ conf n →
     (∀ D:ℕ,Returns Z A v D K p) ∧ VacuumCompat Z A v K p ∧ (∀ D:ℕ,Terminal Z A v D K p)
   indices : ∀ D:ℕ, ∃ W b, Diagnostics (D:=D) A Z W b p
structure Arrives (Z:Ledger L)(P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(A:Ports C)(p:ℕ) : Prop where
   moment : ∀ (n:ℕ) (d:Fin n→ℕ) (v:(i:Fin n)→ Slot C (d i)) (K:Set (Points n)), IsCompact K → K⊆ conf n →
     ∀ q:ℕ, q ≤ p → Cost Z (jointTests K) 0 (A.moments v q) ∧ Cost Z (joins K (Viewers F)) (q+1)
        (fun r (x:Viewers F × Test n)=> measured F (stems L v r) r x.1 x.2 - forecast Z q (A.moments v) r x.2)
   ope : ∀ (n:ℕ) (d:Fin n→ℕ) (v:(i:Fin n)→ Slot C (d i))(D:ℕ)(K:Set (Points n)), IsCompact K → K⊆ conf n →
     ∀ q:ℕ,q ≤ p → Cost Z (jointTests K) 0 (A.ope v D q) ∧ Cost Z (jointTests K) (q+1)
        (fun r ψ=>toFrame L D r (basket P D (stems L v r) r ψ)-forecast Z q (A.ope v D) r ψ)

lemma atOrder (h:Sends Z A p) : Arrives Z P A p := by
    constructor
    · intro n d v K hk he k hl
      obtain ⟨hy,hV,_⟩:= h.mission n _ v K hk he
      exact ⟨hV.cap _ hl,horizonZero Z P H loc hk he hl hV (hy 0)⟩
    intro n d v D K hk he k hl
    obtain ⟨hy,_,hT⟩:= h.mission _ _ v K hk he
    obtain ⟨W,b,hb⟩:= h.indices D
    exact ⟨(hT D).tail _ hl, opeReport Z P H A loc hk he (hy _) (hT D) hb ⟨fun T _ u=>
       let hz:= h.mission 2 _ (T.twins u) _ T.test.hasCompactSupport T.fits; ⟨hz.1 0,hz.2.1⟩⟩ hl⟩
end YM.RG17
