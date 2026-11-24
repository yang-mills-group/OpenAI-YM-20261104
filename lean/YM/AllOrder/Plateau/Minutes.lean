import YM.AllOrder.Plateau.Stoke
-- imports Horizon dust. waiting
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n m: Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ}
local notation "E"=>Positions (Primary n G)
open Trio
lemma agree_turn (s:Signed)(x:Cover)(a:ℕ)(U V: CoverConfig G)(h:Agrees (Lattice.box a) U V): Agrees (Lattice.box a) (pull s 0 U) (pull s 0 V):= by
 let X:= Lattice.box a; have hj x (h:x∈ X): Lattice.affine s (0: Cover) x∈ X:=by unfold X; rw [← box_covariant a s,affine,add_zero]; exact mem_image_of_mem s.act h
 rintro ⟨x,i⟩ hx hy
 have hb:=hj x hx; have he:=hj (x+step i) hy; rw [show Lattice.affine s 0 (x+step i)= Lattice.affine s 0 x+((posDir i).rotate s).vec from (by simp [Lattice.affine, s.act_add, Step.vec_rotate])] at he
 unfold pull; cases hq : ((posDir i).rotate s) with | mk k b =>
 rw [hq] at he; cases b; · exact h (affine s 0 x,k) hb he
 have hv : affine s 0 x-step k∈ X:=by simpa only [show (⟨k,true⟩ : Lattice.Step)=negDir k from rfl, Lattice.Step.vec_neg, sub_eq_add_neg] using he
 exact congr_arg Inv.inv (h (affine s 0 x-step k,k) hv (by change affine s 0 x-step k+step k∈X; rwa [sub_add_cancel]))
variable (A:Packet G k)
abbrev cutA (w:ℕ):= crop w ∘ A
def anchorV (w:ℕ)(n:Side)(x:Site n) (U:Config G n):= Patch.average fun s:Signed=>∑' i,aTerm (cutA A w i) (pull s 0 (expandAt x U))
def gardenfold (w:ℕ)(f: ∀ c:Side, Trio.Offer G c):= ∀ (c m:Side)(x:Site c)(y:Site m)(U:Config G c)(V:Config G m), Agrees (Lattice.box w) (expandAt x U) (expandAt y V)→ f c x U=f m y V
lemma anchor_turn (w:ℕ)(n:Side): Trio.Mirrors (anchorV A w n) := by
 intro x s b V; unfold anchorV; rw [expandAt_pull]; unfold Patch.average; simp_rw [pull_pull,Lattice.affine,Signed.act_zero,add_zero]; -- nested s
 apply congr_arg; exact Equiv.sum_comp (Equiv.mulLeft s) (fun i => ∑' j,aTerm (cutA A w j) (pull i 0 (expandAt _ V)))
lemma anchor_local (w:ℕ): gardenfold w (anchorV A w) := by
 intro c m x y U V h; unfold anchorV Patch.average; apply congr_arg; apply Finset.sum_congr rfl; intro s _; apply tsum_congr; intro i; unfold cutA crop; simp only [Function.comp_apply]; split; next hi =>
    apply aTerm_at; intro e hv hp; let X:= Lattice.box w; let hh(a:Cover)(h:a∈Lattice.box (A i).length):a∈X:=Finset.Icc_subset_Icc (by change _ ≤ _; intros j; apply neg_le_neg; exact Int.ofNat_le.mpr hi) (by intros j; exact Int.ofNat_le.mpr hi) h; exact agree_turn s e.1 w _ _ h _ (hh _ hv) (hh _ hp)
 next hi => simp [aTerm]
lemma anchor_write (w:ℕ)(x:Site n)(s:Signed)(U:Config G n) : (pull s 0 (expandAt x U)) = expandAt (s⁻¹.act x) (pull s 0 U):= by rw [expandAt_pull]; simp only [Lattice.affine, Signed.act_inv, add_zero]
lemma anchor_bill (w:ℕ)(x:Site n)(U:Config G n) : anchorV A w n x U = Patch.average fun s:Signed=> ∑' i,(cutA A w i).unmasked (pull s 0 U) (s⁻¹.act x) := by unfold anchorV; simp_rw [anchor_write w]; rfl; -- maybe omitted A
lemma anchor_whole (w:ℕ)(U:Config G n):∑ x: Site n, anchorV A w n x U= orbitRaw (cutA A w) U:= by
 unfold orbitRaw Precision.uncut; simp_rw [anchor_bill,Patch.average]; rw [← mul_sum,Finset.sum_comm]; apply congr_arg; refine Finset.sum_congr rfl fun s _=> ?_; exact Equiv.sum_comp ((s⁻¹.actEquiv: Site n≃+ Site n).toEquiv) (fun x=> ∑' i, (cutA A w i).unmasked (pull s 0 U) x)
lemma reg_prime (i:Site n) (ha:0<σ)(hb: SumBudget (fun j=>(A j).budget σ) C)(h:∀ j,(A j).Invariant) (p:BudgetPoint) : p.Regular univ (fun U : Config G n=> ∑' j:ℕ,(A j).unmasked U i) := by
 let f (U:Config G n):= ∑' j:ℕ,(A j).unmasked U i; have hs (U:Config G n) : ContDiffAt ℝ (p.order:WithTop ℕ∞) (f ∘ increment U) 0:= by
   let F (M : Work.F02.Ambient G n) := ∑' j, Work.F02.atomExt (A j) i M; let G₁:= Work.F02.physical ∘ increment U; have he : ContDiffAt ℝ ω F (Work.F02.physical (increment U 0)):= (Work.F02.atomExt_series ha hb i (increment U 0)).contDiffAt.restrict_scalars ℝ
   have hh : f ∘ increment U=Complex.reCLM ∘ F∘ G₁:= by ext1 x; rw [Function.comp_apply (f:=Complex.reCLM),Function.comp_apply,Function.comp_apply,show F (G₁ x)=_ from Work.F02.atomExt_real ha hb i (increment U x)]; rfl
   rw [hh]; refine (Complex.reCLM.contDiff.contDiffAt.comp (n:=ω) 0 (he.comp (f:=G₁) 0 ?_)).of_le le_top; refine Work.F02.physical_contDiffAt (A:=increment U) fun i=> ?_; simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
 refine ⟨fun U V h=> congr_arg f (funext (fun i=> h _ (Finset.mem_univ _) (mem_univ _))), Measurable.tsum (fun j=> ((A j).unmasked_cont ..).measurable),?_,fun U _=> hs U, fun U _ A l hl=>Next.Foundations.left_has A hl (hs U) ⟩
 intro x U; apply tsum_congr fun j=>?_ ; unfold Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact h j .. -- fn issue
lemma anchor_reg (ha:0<σ)(hb: SumBudget (fun j=>(A j).budget σ) C)(h:∀ j,(A j).Invariant) (p : BudgetPoint) (w :ℕ) (x:Site n): p.Regular univ (anchorV A w n x):= by
 -- use Seat.reg_charge
 let f (s:Signed)(v:Site n)(U:Config G n):=∑' j,(cutA A w j).unmasked U v; let P (s:Signed):= f s (s⁻¹.act x) ∘ pull s (0:Site n)
 rw [show anchorV A w n x= (Fintype.card Signed:ℝ)⁻¹ • ∑ s':Signed,P s' from funext (fun i=> by rw [anchor_bill]; simp only [Pi.smul_apply, Finset.sum_apply]; rfl)]
 refine AnalyticBridge.CouplingShape.reg_scale _ (Meadow.regularA univ (fun s _=> ?_)); let H:= reg_prime (cutA A w) (s⁻¹.act x) ha (sold A ha hb w) (fun i=>crop_inv w (h i)) p; -- lookup lemma
 exact AnalyticBridge.CouplingShape.reg_extend (WardBin.Wheels.regular_carry s 0 H) (subset_univ _)
end YM.AllOrder.Plateau
