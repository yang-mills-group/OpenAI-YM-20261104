import YM.LocalTaylorR2.Kiln.Till

/-! # Purchase through fixed envelope. The LONG-tail atoms cost at least half the surplus length price on top of the literal χ-renormalizations (coarse parameter). E6 Sales algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
open Itinerary Port Reserves
variable {W :ℝ}
lemma positiveBill (k k' η x :ℝ)(A:ℕ→Atom G d) (i: Trans f):0 ≤ bill k k' η x A i:=by
 unfold bill; have h:= munch A i; split_ifs <;> positivity

def sizing (a x y z:ℝ):= (|y|+ Real.exp (-2*a*till x)* |z|)
lemma style (a X k k' η B:ℝ) (A:ℕ→ Atom G d)(i:Trans f)(P:0≤a)(he : |η|≤ B):
    bill k k' η X A i * Real.exp (2*a*atomCharge A i) ≤ (B*sizing a X k k'*(A i.2.2).magnitude)* Real.exp (2*(2*a)*atomCharge A i):=by
  unfold bill sizing
  generalize hw : (A i.2.2).magnitude = b
  unfold atomCharge; generalize hg : (A i.2.2).length=L'
  have hu : 0 ≤ b:= hw ▸ munch A i
  have hB:0≤B:= (abs_nonneg _).trans he; let t:ℕ:= till X; split
  next h => gcongr <;> first | (apply le_add_of_nonneg_right; positivity) | nlinarith
  next h =>
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (a:=Real.exp (-2*a*till X)* |k'|) (abs_nonneg k)) hB) hu) (Real.exp_pos _).le)
    calc
      _ ≤ B* |k'| * b * Real.exp (2*a*L'):=by gcongr
      _ ≤ B* |k'| * b * Real.exp (-2*a*till X + 2*(2*a)*L'):=by
        have hx:(till X:ℝ) ≤ L':= by exact_mod_cast (le_of_lt (lt_of_not_ge h))
        gcongr; nlinarith
      _ = _:=by rw [Real.exp_add]; ring

-- L slack sufficient: η β price, also extra λ_log lease and θ^p
lemma shops (G:Gauge) (L:Side)(l p d:ℕ)(σ ε a:ℝ)(he:0<ε)(ha:0≤a)(hσ:8*ε<σ)
    {K K' γ :ℝ→ℝ}(hK:Rate G L (-((p+4:ℕ):ℝ)/2) K)(hb:Rate G L 0 K')(hC:Rate G L 0 γ)
    (b χ θ : ℝ)(hx:b≤ 1/2) (hg:χ≤1/2)(hp:-(1/2:ℝ)<θ): ∀ᶠ x in atTop, ∀(c f:Side)(S : StepData c f), S.patch.L=L → ∀ A : ℕ→ Atom G d, SumBudget (fun i => (A i).budget σ) (γ x) → ∀ η, |η| ≤ 2*betaF G x L → Sales (radiusB x) a ε (atomFoot S.ratio l (radiusB x) A) (fun i=>betaF G x L ^χ * (bill (K x) (K' x) η x A i * (betaF G x L ^ b)^p)) (atomCharge A) (betaF G x L^θ):=by
  let Φ (x:ℝ):= betaF G x L; let α x:= Φ x ^b; let Γ x:= Φ x^χ; let u x:= Γ x*(α x)^p; let v x:= (2*Φ x)*sizing ε x (K x) (K' x)
  let g x:= u x * v x; have hr : Rate G L (-((p+4:ℕ):ℝ)/2) (fun x=> sizing ε x (K x) (K' x)) := by
    apply Rate.add (hK.compare (Eventually.of_forall fun i=> (abs_abs _).le))
    have hh:Rate G L (-((p+4:ℕ):ℝ)/2) (fun x=>Real.exp (-2*ε*till x)) := by simpa only [neg_mul] using! (Rate.cutoff (G:=G) (L:=L) (by positivity : 0<2*ε) (a:=-((p+4:ℕ):ℝ)/2))
    simpa only [add_zero] using hh.mul (hb.compare (v:=fun x=> |K' x|) (Eventually.of_forall fun i=> (abs_abs _).le))
  have hq:Rate G L (-(1/2)) g:= by convert! (((Rate.power (G:=G) (L:=L) (a:=χ)).weaken hg).mul (((Rate.power (a:=b)).weaken hx).pow p)).mul ((Rate.hat.mul_left 2).mul hr) using 1; push_cast; ring
  obtain ⟨z,hz,ht⟩:= exists_between hp
  filter_upwards [atom_bills G L L d 0 l (a:=a) (by positivity : 0<2*ε) (show 4*(2*ε)<σ by linarith) ha hq hC (show _ < z from by linarith), ((Rate.power (G:=G) (L:=L) (a:=z)).mul_left (Fintype.card Signed:ℝ)) θ ht, (Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hh hy hp c f S hS A H η hη
  let t : Site f × ℕ → ℝ:= fun i=> g x * (A i.2).magnitude; have hX: 0<betaF G x L:= zero_lt_one.trans_le hp
  have hU:0≤u x:=by unfold u Γ α Φ; positivity
  have hP : 0≤ g x:=by unfold g; apply mul_nonneg hU; unfold v sizing Φ; positivity
  have hv:= hh c f S.ratio (show S.ratio.count=L from hS) _ H t hP (fun i=> ⟨mul_nonneg hP (by unfold Atom.magnitude; positivity), by simp [t]⟩)
  have hm := Sales.price_fst (fun i:Trans f=> t i.2) (atomFoot S.ratio l (radiusB x) A) (atomCharge A) (fun _ => _) (fun s => hv.rotated s 0 ha)
  apply Sales.raise _ (by simpa only [sum_const,card_univ, nsmul_eq_mul] using (le_abs_self _).trans hy : ∑ _ : Signed,Φ x^z ≤ Φ x^θ)
  let z' (i : Trans f) := betaF G x L ^ χ * (bill (K x) (K' x) η x A i * (betaF G x L^b)^p)
  have hNN i:0≤ z' i:= mul_nonneg (by positivity) (mul_nonneg (positiveBill ..) (by positivity))
  refine ⟨hNN,fun i=>budget_mono (hm.hit i) (fun j =>?_) (fun j=>?_)⟩
  · split <;> first | exact mul_nonneg (mul_nonneg (hNN j) (Real.exp_pos _).le) (Real.exp_pos _).le | exact le_rfl
  split
  next h=>
   apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
   unfold tariff; dsimp only; simp only [add_zero]; let Y:= bill (K x) (K' x) η x A j
   calc
    _ = u x * (Y * Real.exp (2*ε* atomCharge A j)) :=by unfold u Y Γ α Φ; ring
    _ ≤ u x * (v x * (A j.2.2).magnitude * Real.exp (2*(2*ε)*atomCharge A j)) := mul_le_mul_of_nonneg_left (style ε x _ _ η _ A j he.le hη) hU
    _ = _ := by unfold t g; ring -- order
  next h=> exact le_rfl
end YM.LocalTaylorR2.Kiln
