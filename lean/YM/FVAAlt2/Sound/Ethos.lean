import YM.FVAAlt2.Sound.Figure
/-! # Uniformly purchase schedules for native formal torus reading before using spatial witness
 Hull.Cost can be arbitrary grown.View scales and even Gamma.Vehicle huge. Φ & not-yet
 numerical receipt. ANY sufficiently big p allowed; one can force other period demands
 here per orbit size/profile before an enlargement. NOT an error assertion on arbitrary
 coadmission's already chosen periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Sound.Ethos
open Function Set Filter MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm Pipeline Pipeline.See Pipeline.Crown Lodge Period.Field PhysicalNext.Repeat.Legato
open Lattice Precision RG Epoch Calibration Rocket Oracle Circuit
open MS MS.Land MS.Dial MS.Rake MS.Vista MS.Fleet MS.Orbit MS.Tone
open PowerSeries Integration RunFormalChain FormalOPE Real Figure
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
open YM.FVAAlt2
-- finite menus
variable {X I:Type}{G:Gauge}{Q:KernelChoices}{M:X→ℕ}{N:Page M→Side}
variable {B:MS.Local.Physical.Deck G}[LinearOrder I][Fintype I]
abbrev MenuF (B:MS.Local.Physical.Deck G)(d:ℕ) := Σ j: Fin (d+1), Plaid B j.val
def owner {d:ℕ}(v:MenuF B d): MS.Rake.Label B := ⟨v.1,v.2⟩
def station (C:ℝ):Finset Cover:= Fintype.piFinset (fun _:Axis=>Finset.Icc ⌊-C⌋ ⌈C⌉)
def carts (C:ℝ) : Finset (I→ Cover):= Fintype.piFinset fun _=> station C -- unused
lemma mark_c (C:ℝ) (v:I→ Cover) (H:∀ i,‖Tone.embed (v i)‖≤ C): v∈ carts C:=by
 refine Fintype.mem_piFinset.mpr fun i=> Fintype.mem_piFinset.mpr fun j=>?_ ; rw [Finset.mem_Icc]; apply And.intro
 · have hx:= ( norm_le_pi_norm ( Tone.embed (v i) ) j ).trans (H i); rw [Real.norm_eq_abs] at hx; change |(v i j:ℝ)| ≤ C at hx; exact_mod_cast (Int.floor_le (-C)).trans (abs_le.mp hx).1 -- exact mod cast wrong expr
 have hx:= (norm_le_pi_norm ( Tone.embed (v i) ) j).trans (H i); rw [Real.norm_eq_abs] at hx; change |(v i j:ℝ)| ≤ C at hx; exact_mod_cast (abs_le.mp hx).2.trans (Int.le_ceil C)
variable (C:Run G){Φ:∀ P:Patch,P.Branches Q G}{R:Circuit M N}(Y: Program Q)(P:SeriesT R Q C.family.path)
variable (Φ) (z:X→ I→ Cover) (F:Calibration.Tent M) (s:ℕ) -- history/p
variable (T:Prescription B) (J:Ledger.Choice M) (θ ε:X→ℝ) (w:X)
-- guard consumer-state after
variable (K:ℝ)(t:X→ℝ)(d p:ℕ)
local notation "runA"=> (Rocket.adjust R Y Φ F (Lodge.basisR C) J)
local notation "per"=> runPer C Φ P
-- const positions w. P Γ.limits possible.
structure Asked (Y:Program Q) (C:Run G) (Φ:∀ P:Patch,P.Branches Q G) (P:SeriesT R Q C.family.path) (F:Calibration.Tent M) (T:Prescription B) (J:Ledger.Choice M)(θ ε:X→ℝ) (K:X→ℝ)(d p:ℕ) (t:X→ℝ) (I:Type) [LinearOrder I] [Fintype I](σ:X→ℕ): Prop where
    answers (w:X) (q:ℕ)(hb:σ w≤q)(D:I→MS.Rake.Label B)(hd:∀ i,(D i).h ≤ d)(z:X→ I→ Cover)
      (hz:∀ i, ‖Tone.embed (z w i)‖ ≤ K w )(j:ℕ)(hj:j≤p): ‖coeff j (runPer C Φ P z (sheet F) q J D T (θ w) (ε w) w) - coeff j (Rocket.adjust R Y Φ F (Lodge.basisR C) J D z T θ ε w)‖ ≤ t w
-- any schedules.Foot δ.~Goal? achieves coordinate convergence for every Compact & identity of cover.L.C receipts too before cutoff.Locations. use finite staffing.
lemma holdings (s:ℕ) (z z': X→ I→ Cover)(w:X)(h:z w=z' w) (D:I→MS.Rake.Label B)(p:ℕ): coeff p (runPer C Φ P z ( Calibration.sheet F ) s J D T (θ w) (ε w) w)= coeff p (runPer C Φ P z' (sheet F) s J D T (θ w) (ε w) w):= samePhase C Φ P z (sheet F) s J D T (θ w) (ε w) w (sheet F) (q:=p) (fun _ _ _=> rfl) z' h p le_rfl
include P in
lemma exactPay (z z':X→ I→ Cover)(w:X)(h:z w=z' w)(D:I→MS.Rake.Label B) (p:ℕ): coeff p (runA D z T θ ε w)= coeff p (runA D z' T θ ε w):=by
    obtain hp:= Figure.tend C Φ Y P z F J D T w θ ε p; obtain hh:= Figure.tend C Φ Y P z' F J D T w θ ε p
    refine tendsto_nhds_unique ( hp.congr (fun i=>?_ ) ) hh
    exact holdings C Φ P F T J θ ε i z z' w h D p
lemma served (K:X→ℝ)(ht:∀ w,0<t w) : ∃ σ:X→ℕ, Asked Y C Φ P F T J θ ε K d p t I σ:=by
 have H(w:X) (D:I→ MenuF B d) (z:I → Cover)(i: Fin (p+1)):= ((Figure.tend C Φ Y P (fun _=>z) F J (owner∘ D) T w θ ε i.val))
 let u(w:X) (q:ℕ)(D:I→ MenuF B d)(z:I → Cover)(i:Fin (p+1)) := coeff i.val ( per (fun _=>z) (sheet F) q J (owner∘D) T (θ w) (ε w) w)
 let V(w:X) (D:I→ MenuF B d)(z:I → Cover) (i: Fin (p+1)):= coeff i.val ( runA (owner∘D) (fun _=>z) T θ ε w )
 have hv(w:X):∀ᶠ q in atTop,∀ D,∀ z ∈ carts (K w),∀ i, ‖u w q D z i-V w D z i‖≤ t w:=by
    refine eventually_all.mpr (fun D=> (eventually_all_finset _).mpr (fun z hz=>eventually_all.mpr (fun i=> ((H w D z i).eventually (Metric.ball_mem_nhds _ (ht w)) ).mono ?_))) -- eventually_all_finset arg?
    exact fun q he=> le_of_lt (by rw [ ← dist_eq_norm ]; exact he )
 choose σ hσ using fun w => eventually_atTop.mp (hv w)
 refine ⟨σ,⟨ fun w q hb D hd z hz j hj=>?_⟩ ⟩
 let d'(i:I): MenuF B d:= ⟨ ⟨(D i).h,Nat.lt_succ_iff.mpr (hd i)⟩,(D i).item ⟩; let l:=fun _:X=> z w
 have hx : owner ∘ d'= D:= rfl; rw [holdings C Φ P F T J θ ε q z l w rfl D j,exactPay C Φ Y P F T J θ ε z l w rfl D j]; exact hσ w _ hb d' (z w) (mark_c _ _ hz) ⟨j,Nat.lt_succ_iff.mpr hj⟩

-- hull for admissible moving schedule.G. all *geometry allowed* absorbed by our Track. Credit at all probes.V_H formal.Label. Not claiming uniform residue at infinitely many F or p before settings. d arbitrary.
section Box
def tot (P:Track X) (x:X):ℝ:= (P.desk.P x+exp (P.Θ x))*P.Θ x
variable {P: Lodge.Track X}{U:X→ Cover}{W:I→ X→ Cover} {μ:ℝ}{l:Filter X}
omit [LinearOrder I] in
lemma eventuallyIn (h:P.VenueT U)(hm:MS.Tide.Profile (P.PoseT μ U W).profile W)(hz:Tendsto P.batch l atTop):∀ᶠ i in l,∀ j:I, ‖Tone.embed (Rocket.Zpose (P.PoseT μ U W) i j)‖≤ tot P i:=by
 refine eventually_all.mpr fun j=> ?_
 obtain ⟨A,hA,hP⟩:= hm j; obtain ⟨B,hB,hv⟩:= h.2.1
 filter_upwards [ ( P.θ_runs hz ).eventually_ge_atTop (max A B) ] with i hi; change ‖Tone.embed (U i+ W j i)‖≤ _; rw [show Tone.embed ( U i + W j i )= Tone.embed (U i) + Tone.embed (W j i) from funext (fun j=>by unfold Tone.embed; simp [ Pi.add_apply]) ]; refine (norm_add_le ..).trans ((add_le_add (hv i) (hP i)).trans ?_); specialize hP i ; unfold tot; rw [ P.payments ]; change B * P.desk.P i+ A*exp (P.Θ i) ≤ _; rw [add_mul]; obtain ⟨ha,hb⟩:= max_le_iff.mp hi; have hp:=P.desk.synchronize i; apply add_le_add <;> nlinarith [ exp_pos (P.Θ i) ]
end Box
end YM.RegulatorIR.FVAAlt2.Sound.Ethos
