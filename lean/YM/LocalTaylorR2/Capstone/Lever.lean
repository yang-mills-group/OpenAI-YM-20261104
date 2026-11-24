import YM.LocalTaylorR2.Capstone.Chart
/-!
 # Rebasing past the Bouquet. Real utterances and parked receipts remain recognizable.

 Tasks including `Meadow.barony` call with `Rain.Zeal.tiers` small calibrated
 volumes, *not* crop the real configurations to uncommon independent θ's. This lemma
 estimates each Offer at correct scale comparing its OWN retained Taylor terms. Couple
 later by `Slide.shape` on the beautiful neighborhood where supBounds are required.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Capstone
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Boulevard
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} (I : Cash W s μ L Q o C T R')
variable {v w δ γ a : ℝ} (b:BudgetPoint) (F : Collection.Source G c)
local notation "M" => Beam.marquee I b

def trestle (x: Site c) := ∑ i∈Meadow.panel I n, Meadow.garnerAt I b x i • F.logRead i
-- make `n` explicit for readability
abbrev stepsAt (k:ℕ): Trio.Offer G c:= trestle I b F (n:=k)
lemma terms_bloom (X:Alliance I H 1 0)(hp:R'.path=R.path)(he:I.supportP=H.supportP)(hz:X.units=Equiv.refl _)(γ:ℝ) (χ:Chi) (n:ℕ): Meadow.barony H χ n γ = stepsAt I b (plusone I X χ γ) n:= funext (fun x=> Meadow.aster χ b X hp he hz γ n x)
variable {y w z : Collection.Source G c} (hx : Meadow.Budget b (Beam.marquee I b).reg F.logRead v) (n:ℕ)
lemma total : Trio.froth (stepsAt I b F n) = ∑ i∈Meadow.panel I n,F.logRead i := by
  funext V; dsimp only [Trio.froth,stepsAt,trestle]; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [sum_comm]; simp_rw [← sum_mul,Meadow.paysOne,one_mul]
lemma terms_chain (hp:y.logRead=w.logRead+z.logRead): stepsAt I b y n=stepsAt I b w n+stepsAt I b z n:= by funext x; unfold stepsAt trestle; rw [hp]; simp only [Pi.add_apply,smul_add,sum_add_distrib]
include hx
lemma watch (x:Site c): b.Regular univ (stepsAt I b F n x):=by
  obtain ⟨k,h,hK⟩:= hx; exact Meadow.regularA _ (fun i _=>CouplingShape.reg_scale _ (CouplingShape.reg_extend (hK i).1 (subset_univ _))) -- lemma type
lemma coffee (V:Config G c) (hp: flags b.threshold V=∅) (l:List (Directions G c)) (he:l.length ≤ b.order)(ho:∀ i∈l,‖i‖≤ b.threshold):
    ‖leftDerivs (Trio.froth (stepsAt I b F n)) l V‖ ≤ (Fintype.card (Site c):ℝ)*v:=by
  let Z i:= leftDerivs (F.logRead i) l V
  obtain ⟨k,h,hK⟩:=hx; have hF:= Boulevard.planetary h (fun i=>(hK i).2.1); let D:=Meadow.panel I n
  have hP i : Healthy b.threshold ((M).reg i).support V:= by unfold Healthy; rw [hp]; simp
  rw [total, Push.Local.left_sum _ _ _ _ (fun i _=> (hK i).1.smooth V (hP _)) he]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=> (hK i).2.2 V (hP i) l he (fun v hv=> tiny (ho v hv) ((M).reg i).site))).trans (budget_sum hF D))
lemma rails (V:Config G c) (hp: flags b.threshold V=∅) (l:List (Directions G c)) (he:l.length ≤ b.order)(ho:∀ i∈l,‖i‖≤ b.threshold):
    ‖leftDerivs (Boulevard.stillA (Trio.froth (stepsAt I b F n))) l V‖ ≤ 2*(Fintype.card (Site c):ℝ)*v:=by
  let u:=Trio.froth (stepsAt I b F n); let y₀ (_:Config G c):= u 1
  have ht:b.Regular univ u := by
    rw [show u = ∑ i : Site c, stepsAt I b F n i from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ (fun j _=> watch I b F hx n j)
  have hv':Healthy b.threshold (univ:Support c) V:=by unfold Healthy; rw [hp]; simp
  have h1 : ‖leftDerivs y₀ l V‖ ≤ ‖u 1‖:= by cases l <;> simp only [y₀,Work.G07.left_const]; all_goals simp
  have hy : ‖u 1‖≤ (Fintype.card (Site c):ℝ)*v:= coffee I b F hx n 1 (UVNext.CouplingReset.flags_one _) [] (by simp) (by simp)
  change ‖leftDerivs (u-y₀) l V‖ ≤ _
  rw [VerifiedReset.left_sub (ht.smooth _ hv') (show Push.Local.Chart b.order y₀ V from contDiffAt_const) he]; have h:‖leftDerivs u l V‖≤ (Fintype.card (Site c):ℝ)*v := coffee I b F hx n V hp l he ho
  exact (norm_sub_le ..).trans ((add_le_add h (h1.trans hy)).trans_eq (by ring))
end YM.LocalTaylorR2.Capstone
