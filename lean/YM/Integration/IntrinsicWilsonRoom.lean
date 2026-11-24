import YM.Integration.IntrinsicReaderComparison

/-! Uniform admission of the separated continuum room on the physical engineering mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicWilsonRoom
open PhysMS Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards OPE.Log
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open SharedIntrinsicWilsonGrid IntrinsicWilsonTensor
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

theorem radius_rate {α : Type*} {l : Filter α} {T : α → ℝ} {j : α → ℕ} {c : ℝ}
    (hT : Tendsto T l atTop) (hj : Height C.S l T j c) :
    RateLE l T (fun t => ((C.path.levels.budget (j t)).B:ℝ)) 0 := by
  let beta (t : α) := C.path.levels.clock.hatBeta (j t)
  have b : RateLE l T beta 0 := ((OPE.Log.betaStamp (C:=C) hT hj).zeroCost hT).pays hT
  have square : RateLE l T (fun t => beta t ^ (2:ℕ)) 0 := by simpa only [mul_zero] using b.pow 2 hT
  apply (square.add (RateLE.const (1:ℝ) hT) hT).transfer
  filter_upwards with t
  have positive : 1 < beta t := C.path.levels.fits.delayed (j t)
  have ceil : ((C.path.levels.budget (j t)).B:ℝ) ≤ (Real.log (beta t))^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log (beta t)))).le
  have logle : (Real.log (beta t))^2 ≤ (beta t)^2 :=
    pow_le_pow_left₀ (Real.log_nonneg positive.le) (Real.log_le_self (by linarith)) 2
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity)]
  exact ceil.trans (by linarith)

omit [Fintype I] in
/-- Every central grid configuration in the normalized separated room is
admissible for the same three physical heights and original cell. -/
theorem admits {n m : ℕ} (P : Plan C D n m) (M η : ℝ) (hη : 0<η) :
    ∀ᶠ t in trail, ∀ x : I → Cover, WithinRoom t M η (fun i => C.S.gridPoint (P.j t) (x i)) 0 →
      Plot C (P.b t) (P.middle t) (P.j t) x := by
  let hT := PhysMS.to_log_zoom
  have next := (P.mid.step C.path.levels.fits.mesh).mesh
  have near := next.overtakes ((RateLE.const (8*M) hT).mul (PhysMS.length_rate.pays hT)) hT (by linarith [P.low])
  have B := (radius_rate hT P.fine).pow 2 hT
  have fine := ((RateLE.const (2:ℝ) hT).mul (P.fine.mesh.pays hT)).mul B
  have sep := ((RateIs.const hT hη).mul PhysMS.length_rate).overtakes fine hT (by simp only [zero_add,mul_zero,add_zero]; linarith [P.high])
  filter_upwards [near,sep,P.coarse.earlier P.before hT P.mid,P.mid.earlier (P.low.trans P.high) hT P.fine] with t fit gap first last
  intro x hx
  refine ⟨fun i => ?_,fun i j hij => gap.trans_le (hx.spaced i j hij),first.le,Nat.succ_le_of_lt last⟩
  have hit := hx.span i
  rw [sub_zero] at hit
  exact (mul_le_mul_of_nonneg_left hit (by norm_num : (0:ℝ)≤8)).trans_lt (by simpa only [id_eq,mul_assoc] using fit)

/-- Compare the original extracted tensor with the physical Reader on all normalized separated grid configurations. -/
theorem coupling (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (hF : Foundation F R) (M η : ℝ) (hM : 0≤M) (hη : 0<η) :
    ∃ Z : ℝ → (I → Cover) → Tensor C d D,
      (∀ᶠ t in trail, ∀ x : I → Cover, WithinRoom t M η (fun i => C.S.gridPoint (P.j t) (x i)) 0 →
        Common F R J t (P.b t) (P.j t) x (Z t x)) ∧
      ∀ (g : ℝ → ℝ), Coupling G g → ∀ (k : ℕ) (ε : ℝ), 0<ε →
        ∀ᶠ t in trail, ∀ x : I → Cover,
          let y := fun i => C.S.gridPoint (P.j t) (x i)
          WithinRoom t M η y 0 → ∀ v : (i : I) → Input C (d i),
            ‖(J t D).symm (S.project D (Z t x v) - R.packet D y (Frame.born J t v) 0)‖ ≤
              ε*g t^k * ∏ i, ‖v i‖ := by
  obtain ⟨Z,actual,_⟩ := PhysicalWilsonTensorReadout.engineering F facility anchor R P J H
  have ok := admits (I:=I) P M η hη
  refine ⟨Z,?_,?_⟩
  · filter_upwards [actual,ok] with t select grid
    exact fun x room => select x (grid x room)
  intro g hg k ε hε
  filter_upwards [IntrinsicReaderComparison.coupling F facility anchor R P J H hF M η hM hη g hg k ε hε,ok,actual]
    with t close grid select
  intro x y room
  exact close x (grid x room) room _ (select x (grid x room))

end YM.Integration.IntrinsicWilsonRoom
