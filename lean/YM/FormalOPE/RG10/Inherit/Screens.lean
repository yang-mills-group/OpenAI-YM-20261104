import YM.FormalOPE.RG10.Inherit.Charges
/-!
 # Restricting gauge invariant multi-edge probes
 Bounded costs hold for every layer and truss, even though `Credential` consumers do NOT assume
 it in general. Use local smoothness smooth not analytic label. ContDiffAt ℝ ∞.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart Lattice RG
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{f:Side}{E:Type}[Fintype E]
variable (L:Fabric G f)(T R : L.loom.Truss)

structure Curtain (a: Spending G E): Prop where
 meas : Measurable a
 bounded : ∃ R:ℝ,∀ u,‖a u‖≤R
 germ : ContDiffAt ℝ ∞ (a ∘ expLinks G E) 0
lemma unit : Curtain (1:Spending G E):= ⟨measurable_const,⟨1,fun _=> by simp⟩, contDiffAt_const⟩
lemma Curtain.transfer {I:Type}[Fintype I](X:Atelier G I E){a:Spending G E}(H:Curtain a): Curtain (a ∘ X.placement) where
 meas:= H.meas.comp X.placement.measurable
 bounded:= H.bounded.imp (fun M h x=> h _)
 germ := by
   have he:= (show ContDiffAt ℝ ∞ (a ∘ expLinks G E) (X.prepare 0) from X.prepare_zero.symm ▸ H.germ).comp (0:Direction G I) (X.prepare_form.of_le le_top)
   exact he.congr_of_eventuallyEq (X.prepare_apply.symm.fun_comp a)
lemma Curtain.mul {a b:Spending G E}(A:Curtain a)(B:Curtain b): Curtain (a*b) where
 meas:= A.meas.mul B.meas
 bounded:= by
  obtain ⟨m,h⟩:= A.bounded; obtain ⟨n,i⟩:= B.bounded; refine ⟨m*n,fun u=>?_⟩; rw [Pi.mul_apply,norm_mul]; exact mul_le_mul (h _) (i _) (norm_nonneg _) ((norm_nonneg _).trans (h 1))
 germ := A.germ.mul B.germ
lemma Curtain.gather {I:Type}(s:Finset I)(a:I→Spending G E)(H:∀ i∈s,Curtain (a i)):Curtain (∏ i∈s,a i):= by
 induction s using Finset.induction with
 | empty => simpa using (unit (G:=G) (E:=E))
 | @insert i s h ih => rw [Finset.prod_insert h]; exact (H i (by simp)).mul (ih (fun j hj=> H j (by simp [hj])))

lemma premium_cont (L:Fabric G f) (a:L.Accounts): Continuous (fun u=> premi L u a):= by
 cases a
 · exact Orb.continuous_account.comp (continuous_pi (f:=fun u:Booth L=>u∘Sum.inl) fun i=> continuous_apply (Sum.inl i))
 rename_i i
 exact (Fabric.areal L i).comp (continuous_pi (f:=fun u:Booth L=> u∘ Sum.inr) fun i=> continuous_apply (Sum.inr i))
lemma componentProbe (a:L.Accounts): Curtain (fun u=>L.price (T.board u) a) where
 meas:= (punctual L T a).meas
 germ:= (punctual L T a).smooth.of_le le_top
 bounded:= by
   obtain ⟨m,H⟩:= isCompact_univ.exists_bound_of_continuousOn (premium_cont L a).continuousOn
   refine ⟨m,fun x=>?_⟩; rw [accurate L T]; exact H _ (Set.mem_univ _)
lemma also {F:L.LinksOn→ℝ} (h:L.Reading F)(A:Curtain (F ∘ R.board)): Curtain (F ∘ T.board):= by
 have he: (F ∘ R.board) ∘ (reset L.loom T R).placement=F ∘ T.board:= by
  ext1 x; change F (R.board (T.transfer R x)) = _; rw [Loom.Truss.transfer_spin]; exact h.leg _ (R.frame_root _) (T.board x)
 rw [←he]; exact A.transfer _
-- multispectral from only *one* truss, avoiding assuming dependence impossible
structure Multipurpose (F:L.LinksOn→ℝ): Prop where
 reading : L.Reading F
 required : ∃ R:L.loom.Truss, ContDiffAt ℝ ∞ ((F ∘ R.board) ∘ expLinks G R.Bulk) 0
lemma Multipurpose.passes {F:L.LinksOn→ℝ}(h:Multipurpose L F): Curtain (F ∘ T.board):= by
 obtain ⟨R,hR⟩:= h.required
 exact also L T R h.reading ⟨h.reading.meas.comp R.board_cont.measurable,h.reading.bounded.imp (fun _ h x=> h _),hR⟩
lemma basic : Multipurpose L 1:= ⟨L.house,⟨L.atop, contDiffAt_const⟩⟩
end YM.FormalOPE.RG10.Inherit
