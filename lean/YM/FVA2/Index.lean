import YM.PertExtension.OrbExpansion
import YM.XSpace.Tree

/-!
# One-link-per-orbit orientations

Haar Jacobian and localization threshold for use of XSpace tree prescription with RG10.
No lower bound on side used besides `Period` (which includes ≥4 and even).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2
open MeasureTheory Set Function Lattice XSpace PertExtension
open scoped Topology BigOperators Classical ENNReal
namespace Reg
variable {G:Gauge}(R:XSpace.Period)
local notation "n"=> R.side

@[simp] lemma reflect_eq (e:R.Bonds): R.reflect e= Orb.reflect e:=rfl
lemma same_fold (e:R.Bonds) : R.rep (Orb.eR e)=R.rep e:=by
 rcases Orb.eR_spec e with h|h
 · rw [h];
 rw [h,← reflect_eq,R.rep_reflect]

def edges : R.Link ≃ Orb.OEdge n where
 toFun e:=Orb.index e.val
 invFun e:= R.rep e.val
 left_inv e:=by change R.rep (Orb.eR e.val)=e; rw [same_fold,R.rep_fixes]
 right_inv e:=by
   apply Subtype.ext
   change Orb.eR (R.rep e.val).val=e.val
   by_cases h:R.Chosen e.val; rw [R.rep_chosen e.val h,e.property]
   rw [R.rep_other e.val h, reflect_eq, Orb.eR_reflect,e.property]

/-- Coordinate change at the link, before all tree elimination. -/
def asOrb (U:R.Array G)(i: Orb.OEdge n):G.El:=R.restore U i.val
lemma recover (U:R.Array G) : Orb.liftLinks (asOrb R U)=R.restore U:=by
 funext x
 by_cases h:Orb.eR x=x
 · rw [Orb.liftLinks,if_pos h]; change R.restore U (Orb.eR x)=_; rw [h]
 rw [Orb.liftLinks,if_neg h]
 change (R.restore U (Orb.eR x))⁻¹=_; rw [(Orb.eR_spec x).resolve_left h, ← reflect_eq, R.restore_reflect, inv_inv]
lemma volume_change (G:Gauge) : MeasurePreserving (asOrb R) (R.measure G) (Chart.physical G (Orb.OEdge R.side)):=by
 let K:= Orb.OEdge R.side
 let T(i:K)(u:G.El): G.El:=if R.Chosen i.val then u else u⁻¹
 have hT (i:K) : MeasurePreserving (T i) G.probHaar G.probHaar:=by
    dsimp only [T]; by_cases h:R.Chosen i.val
    · simpa only [if_pos h] using! MeasurePreserving.id G.probHaar
    simpa only [if_neg h] using! G.preserve_inv
 let Gx:= MeasurableEquiv.arrowCongr' (edges R) (MeasurableEquiv.refl G.El)
 have h:= measurePreserving_arrowCongr' (fun _:R.Link=> G.probHaar) (fun _:K=> G.probHaar) (edges R) (MeasurableEquiv.refl G.El) (fun _=>MeasurePreserving.id _)
 exact (measurePreserving_pi _ _ hT).comp h

/-- Expose the `Orb` top slice integral in terms of the XSpace Link array. For all equivariant-site-gauge
invariant continuous functions on the physical links. -/
theorem compare (F: Wilson.Config G R.side→ℝ)(hc:Continuous F)
    (h:∀ t : Site n → G.El, (∀ x,t (-x)=t x) → ∀ U, F (gauge t U)=F U) :
    (∫ u, F (R.restore u) ∂ R.measure G) = (∫ u:Orb.Slice G R.side,F (Orb.links 1 u) ∂ Chart.physical G (Orb.Cotree n)):=by
 have he:= volume_change R G
 have hf: (F ∘ Orb.liftLinks) ∘ Reg.asOrb R = F ∘ R.restore (G:=G):=by rw [comp_assoc, show (Orb.liftLinks ∘ Reg.asOrb R)=_ from funext (recover R (G:=G))]
 calc
   _ = (∫ u:R.Array G, (F ∘ Orb.liftLinks ∘ asOrb R) u ∂ R.measure G):= by rw [← comp_assoc,hf]; rfl
   _ = (∫ u: Orb.OEdge n → G.El, F (Orb.liftLinks u) ∂ Chart.physical G _):=by
     rw [← he.map_eq]; exact (integral_map he.aemeasurable (show AEStronglyMeasurable (F ∘ Orb.liftLinks) _ from (hc.comp (Orb.lift_cont G)).aestronglyMeasurable)).symm
   _ = _:= Orb.average_eq G F hc (even_iff_two_dvd.mpr R.even) h

/-! We can even transfer the nonabelian flat uniqueness argument (fixed saddle expansion
needs only localization here, but this approach permits arbitrary trees with no extra window). -/
lemma flat_gauged {U:R.Array G}(h:Wilson.energy (R.restore U)=0) :
    ∃ t: Site n → G.El, (∀ x,t (-x)=t x) ∧ gauge t (R.restore U)=1:=by
 let e:Even R.side.val:=even_iff_two_dvd.mpr R.even
 let A:=asOrb R U; let b(i:Orb.Trees n):=A i.val; let y(i:Orb.Cotree n):=A i.val
 have hs:Orb.splitLink b y=A:= funext fun i=>by unfold Orb.splitLink; split <;> rfl
 have hx:R.restore U=Orb.links b y:=by unfold Orb.links; rw [hs]; exact (recover ..).symm
 let t:=Orb.frame b
 refine ⟨t,Orb.frame_neg _,?_⟩
 rw [hx]; change Orb.aligned b y=1
 have hv:=Orb.alignment e b y
 have ht:=Wilson.energy_gauge (R.restore U) t; rw [h,hx] at ht; change Wilson.energy (Orb.aligned b y)=0 at ht; rw [hv] at ht
 rw [hv,Orb.flat_unique e ht]; funext i
 change (if Orb.eR i=i then _ else _) = (1:G.El)
 have hq (z): Orb.splitLink (K:=G.El) (1:Orb.Trees R.side→G.El) 1 z=(1:G.El):=by unfold Orb.splitLink; split <;> rfl
 change (if Orb.eR i=i then Orb.splitLink 1 1 (Orb.index i) else (Orb.splitLink 1 1 (Orb.index i))⁻¹) = _
 simp [hq] -- fn=1

variable {R}
/-- The full finite action used by XSpace, on its tree slice. -/
abbrev bill (T:R.Tree)(v:T.Slice G):ℝ:=R.energy (T.drape v)

set_option maxHeartbeats 500000 in
lemma flat_unique (T:R.Tree){V:T.Slice G}(h:bill T V=0) :V=1:=by
 let U:=R.restore (T.drape V)
 obtain ⟨t,he,hf⟩:= flat_gauged R (U:=T.drape V) (show Wilson.energy U=0 from by change Wilson.energy U / 2=0 at h; linarith)
 let q:R.Vertex→ G.El:= Quotient.lift t (by intro x y (h:y=x ∨ y=-x); rcases h with h|h <;> simp [h,he])
 have hx : t=q ∘ R.vertex:=rfl
 rw [hx, ←R.act_restores] at hf
 have hR1 : R.restore (G:=G) 1=1:=funext (fun i=>by simp [Period.restore])
 have hv:= R.restore_injective (hf.trans hR1.symm)
 have oneStep (x:R.Vertex)(h:x≠T.root) : q (T.parent x)=q x:=by
    let i:=T.edge x h
    have ht:=congr_fun hv i
    change q (R.src i)*T.drape V i* (q (R.dst i))⁻¹=1 at ht
    rw [show T.drape V i=(1:G.El) from T.drape_tree _ ⟨i,(T.mem_edges _).mpr ⟨x,h,rfl⟩⟩,mul_one,mul_inv_eq_one] at ht
    rcases T.joins x h with ⟨a,b⟩|⟨a,b⟩
    · unfold i at ht; rw [a,b] at ht; exact ht.symm
    unfold i at ht; rwa [a,b] at ht
 have common (m:ℕ): ∀ x,T.rank x=m → q x=q T.root:=by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hm; by_cases h:x=T.root
      · subst x; rfl
      exact (oneStep x h).symm.trans (ih _ (hm ▸ T.closer x h) _ rfl)
 funext i; have ht:= congr_fun hv i.val
 change q (R.src i.val)* T.drape V i.val*(q (R.dst i.val))⁻¹=1 at ht
 rw [T.drape_free, common _ (R.src i.val) rfl,common _ (R.dst i.val) rfl,mul_inv_eq_one, mul_eq_left] at ht; exact ht
end Reg
end YM.FVA2
