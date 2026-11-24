import YM.FormalBulk08.Plait.Wax
import YM.FormalBulk08.Mesa.Main
import YM.FormalBulk08.Bank.Tee
import YM.Push.SECTOR_MEASURE.Presented

/-! ### Expansion object, same pure Wilson construction.

Config prior is probability (Haar). Density orientation matters. Logs of sampler
are taken for the field-dependent factors, never as a tack-on expansion of the
likelihood: the common choices are *accounted and summed*. This only certifies
a germ, and does not justify using it instead of the actual choice-dependent
processor in a local analytic error proof.

Chart variables in the coefficient prescriptions are divided by the coupling.
E.g. log(U_f)=g_f*A here on every off-tree link in absolute tree gauge.
`paste` includes power g already; multiply by inv g^2 by `afterX . 2`. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Primer
open Lattice Laurent Bloch RG Wilson Filter Function Precision Set MeasureTheory
open Work.F05 Next.Free Reef Flat Orb Wick Series Mesa Jets Tree
open PowerSeries
open Stationary hiding shine Rays
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}(S:StepData c f)(t:S.Choices)(F: Forest S.ratio){P: ChartRatio G}

/-- Original sampler normalizes on *coarse* field. Its germ, exact with
configuration-independent denominator, in all absolute log coordinates (of course
NOT expansion of the actual integral). -/
lemma density_germ (h:S.patch.Branches S.kernel G) :
    (∀ β:ℝ,S.IsKernel β G) ∧ (∀ β:ℝ,0 < S.penaltyZ β G) ∧
     ∀ᶠ x:Rays (Glob G c f) in 𝓝 0, ∀ β:ℝ,
         S.density β (input G f (x ∘ Sum.inl)) (input G c (x ∘ Sum.inr))
         = (S.penaltyZ β G)⁻¹ ^ Fintype.card (Edge (Site c)) * Real.exp (-β * clack S t x) := by
    refine ⟨fun β=>S.isKernel h β,fun β=> S.penaltyZ_pos β,?_⟩
    have hx:Tendsto (fun x:Rays (Glob G c f)=> input G f (x ∘ Sum.inl)) (𝓝 0) (𝓝 1):= by
        let U:= fun x:Rays (Glob G c f)=>x ∘ Sum.inl (β:=wire G c)
        have hv: ContDiffAt ℝ ω U 0:= contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
        have hg:U 0=0:=rfl
        simpa only [hg, input, ContinuousLinearEquiv.map_zero,link_one] using! (Army.powL (G:=G) hv).cont.tendsto
    filter_upwards [hx.eventually (clamor S h t)] with x hp β; rw [hp]
    unfold clack noiseTaylor StepData.noise StepData.penaltyWeight
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← Real.exp_sum]
    congr 2; rw [←Finset.mul_sum,mul_assoc];rfl

variable {S}
/-- Period-by-period preparation for the integrals this assignment expands
FORMALLY. No use of a saddle far from zero. `parcel` is local only. AxisChart
uses ordinary `volume`; `stand` is a fixed linear change of variables (coordinate
choice doesn't couple to coarse field). Exposure for absolute links. -/
lemma Haar_on_slice (F:Forest S.ratio)(h:LocalRatio P) :
    parcel F P ∈ 𝓝 (0:AxisChart G F) ∧ ∀ (Z : Set (AxisChart G F)), IsCompact Z→ Z ⊆ parcel F P→
       F.order G (exposure F 0 '' Z)= ∫⁻ y in Z, ENNReal.ofReal (P.scale ^ Fintype.card F.Free * sap F P ((Reef.stand G F).symm y)):= by
   refine ⟨parcel_zero F h,fun Z hz hp=>?_⟩; rw [order_exposed F h _ _ hz hp]; simp [sap,load_eq]

/-- Reuse the proved gauge rule on the ACTUAL data. Any tree; log germs
will use an exposed slice on the same StepData. -/
lemma history_uses_slice (H:History G)(h:H.Selected)(i N q:ℕ)(he:i<N):
    let S:=H.levels.clock.op i q; let R:= H.rep N q (i+1); ∀ F:Forest S.ratio, ∀ V:Config G (H.S.side i q),
    (H.rep N q i).eval V = ∫ x:F.Slice G,S.density R.beta (F.drape x) V * R.eval (F.drape x) ∂F.order G:= by
   intro S R F V; rw [(h.steps N q i he).1]; exact F.pushing (H.levels.transition_mass i q R.beta) _ V (Push.SectorMeasure.Presented.lawful_gi (h.represents N q (i+1) he).good) ((R.envelope (h.represents N q (i+1) he).good).integrable _) (fun k U=>(H.levels.blocks i q).gauge R.beta U V k)

lemma fine_equates :f=c*S.patch.L:=Subtype.ext S.sizes
lemma step_joint (S:StepData c f): HEq S (primary S.patch S.kernel c) := by
   obtain ⟨P,K,h⟩:=S; replace h:f=c*P.L:=Subtype.ext h; subst f; rfl

/-- A primary Flight taken from the physical series has exactly the same
block operation & ratio & branches on each period. -/
lemma at_physical (A:Levels G)(i p N:ℕ):
     let S:= primary (destination A N i).patch A.clock.kernel (A.S.side i p)
     HEq (A.clock.op i p) S ∧ S.patch.Branches S.kernel G:= by
   intro S; exact ⟨step_joint (A.clock.op i p),(A.blocks i p).branches⟩

variable (S)
/-- All field-dependent factors included in the coefficient sampler.
 `Reef.seat` restricts any fine input/mask-free production to this slice. -/
lemma prepare (F:Forest S.ratio)(p:Pap (wire G f))(h:S.patch.Branches S.kernel G)(t:S.Choices)(hv:LocalRatio P):
    let A x:= sap F P (x ∘ Sum.inl (β:=wire G c));
    X^2 * flush F t P p = X^2 * Reef.seat F p - paste (clack S t ∘ graft F)
                + X^2 * paste (Real.log ∘ A) := by
   intro A
   have he: Jets.halo (sap F P) (wire G c)=paste (Real.log ∘ A):= by
       rw [Jets.halo, ←Plait.pin_rung _ (sap_root F P hv) (sap_smooth F P hv)]
       refine (folds_byte (Sum.inl (β:=wire G c)) (Real.log ∘ sap F P) ?_).symm
       exact (sap_smooth F P hv).log (by rw [sap_root F P hv];exact one_ne_zero)
   have hm:= salute (G:=G) S h t
   rw [flush,he,mul_add,vacuumU,map_sub,mul_sub, Reef.seat]
   rw [paste_steps (clack S t) (graft F) ((discord S h t).of_le le_top) ((graft_receipt F).of_le le_top) (graft_origin F),←hm,_root_.map_mul,map_pow]
   rw [show roam ℝ _ X=X from Series.change_X (insertAt _ (motor (graft F)))]
end YM.FormalBulk08.Primer
