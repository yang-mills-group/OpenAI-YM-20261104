import YM.Integration.ActualOriginalQFrozenInput

/-! Coordinate invoices for the finite-jet readers of actual original source packets.
The fixed signed frame weights are chosen once for each Taylor degree.  The original
test sheet, inverse scale, factorial, orientation and marked site occur explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalSourceJetAddresses
open Function Finset Lattice Wilson RG Source Labels Marker Tensor RG05Readout.Native
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Extra.Histories
open ActualRunCalibrationTests NativeCalibrationMoodReadout QlocalOrientedTests
open PertExtension ActualRunCurvaturePackets ActualRunKernelPackets NativeCurvatureTensor
open Comparison.Density.RenderM ActualRunPacketRetuning
open scoped Classical BigOperators ContDiff

abbrev Word (k : ℕ) := Fin k → Axis

def axes : Module.Basis Axis ℝ E4 := (Pi.basisFun ℝ Axis).map coordinates.toLinearEquiv

def sample (k : ℕ) : Orb k →ₗ[ℂ] (Word k → ℂ) where
  toFun T w := T.val (axes ∘ w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem samples_determine (k : ℕ) : Injective (sample k) := by
  intro T U h
  apply Subtype.ext
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  exact Module.Basis.ext_multilinear (fun _ => axes) (fun w => congr_fun h w)

/-- A fixed reconstruction on the native symmetric Taylor tensors. Its values
on axis indicators are the entire, pre-test list of address coefficients. -/
def recover (k : ℕ) : (Word k → ℂ) →ₗ[ℂ] Orb k :=
  ((sample k).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (samples_determine k))).choose

def weight (k : ℕ) (b : Beam k) (w : Word k) : ℂ :=
  writeC k (recover k (Pi.single w 1)) b

theorem frame (k : ℕ) (b : Beam k) (T : Orb k) :
    writeC k T b = ∑ w, weight k b w * sample k T w := by
  have left : (recover k).comp (sample k) = LinearMap.id :=
    ((sample k).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (samples_determine k))).choose_spec
  let L : (Word k → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.proj (R := ℂ) (φ := fun _ : Beam k => ℂ) b ∘ₗ (writeC k).toLinearMap ∘ₗ recover k
  have hrow : L (sample k T) = writeC k T b :=
    congrArg (fun Z => writeC k Z b) (LinearMap.congr_fun left T)
  rw [←hrow]
  conv_lhs => rw [←(Pi.basisFun ℂ (Word k)).sum_repr (sample k T)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_smul, Pi.basisFun_repr, Pi.basisFun_apply, smul_eq_mul, mul_comm]
  rfl

/-- The undivided derivative at its actual physical point. -/
def jet (k : ℕ) (w : Word k) (z : Pos) (f : Pos → ℂ) : ℂ :=
  iteratedFDeriv ℝ k f z (fun j => Pi.single (w j) 1)

def price (k : ℕ) (b : Beam k) : ℝ := ∑ w, ‖weight k b w‖

def multiplier {d : ℕ} (i : Letter d) (r : ℝ) (w : Word (depth i)) : ℂ :=
  ((r ^ depth i * ((depth i).factorial : ℝ)⁻¹ : ℝ) : ℂ) * weight (depth i) i.2 w

/-- Native RG05 calibrated Taylor reading as one finite address row. No test
is involved in selecting the weights, its point, or its derivative orders. -/
theorem readout (U : Orbit) {d : ℕ} (i : Letter d) (hi : depth i ≤ U.D)
    (δ : E4) (r : ℝ) (f : U.Mood) :
    NativeCalibrationMoodReadout.readout U i hi δ r f =
      ∑ w, multiplier i r w * jet (depth i) w (coordinates.symm δ) f.val := by
  let k := depth i
  have hf := (U.admits f).choose_spec.orders
  have hs : ContDiff ℝ (k : WithTop ℕ∞) (f.val ∘ coordinates.symm) :=
    (hf.of_le (Nat.cast_le.mpr hi)).comp coordinates.symm.contDiff
  let T : Orb k := ⟨Tensor.coeff (f.val ∘ coordinates.symm) k δ, Tensor.coeff_symm hs.contDiffAt⟩
  change ((r ^ k : ℝ) : ℂ) * writeC k T i.2 = _
  rw [frame, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hjet : sample k T w = (((k.factorial : ℝ)⁻¹ : ℝ) : ℂ) * jet k w (coordinates.symm δ) f.val := by
    change (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k (f.val ∘ coordinates.symm) δ) (axes ∘ w) = _
    rw [show (f.val ∘ coordinates.symm) = f.val ∘ coordinates.symm.toContinuousLinearMap from rfl,
      ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ (Nat.cast_le.mpr hi)]
    simp [smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      axes, jet, Function.comp_def, Complex.real_smul, k]
  rw [hjet]
  simp only [multiplier, Complex.ofReal_mul]
  ring

private theorem jet_conjugate (U : Orbit) (f : U.Mood) {k : ℕ} (hk : k ≤ U.D)
    (w : Word k) (z : Pos) : jet k w z (conjugateMood U f).val = star (jet k w z f.val) := by
  change (iteratedFDeriv ℝ k (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap ∘ f.val) z) _ = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ (U.admits f).choose_spec.orders.contDiffAt (Nat.cast_le.mpr hk)]
  rfl

/-- Correct native orientation for each signed source; complex conjugation
acts on the fixed coefficient when evaluated on an ordinary complex test. -/
theorem oriented (U : Orbit) (t : Motion) (c : ℂ) {d : ℕ} (i : Letter d)
    (hi : depth i ≤ U.D) (δ : E4) (r : ℝ) (f : U.Mood) :
    QlocalSignedReadout.native U t c i hi δ r f = ∑ w,
      Motion.scalar t (c * multiplier i r w) * jet (depth i) w (coordinates.symm δ) f.val := by
  rw [QlocalSignedReadout.native, QlocalSignedReadout.linear_apply, readout, Finset.mul_sum]
  cases h : t.2 <;>
    simp only [Motion.scalar,orientedMood,h,Bool.false_eq_true,if_false,if_true,jet_conjugate U f hi,mul_assoc]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [star_mul,star_star]
  ring

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

omit [DecidableEq V] [Fintype V] in
/-- Every primitive fixed-Q source coefficient on the actual Run. Its mark and
its finite address, scale, and original glyph remain independently specified. -/
theorem original (s : ActualOriginalQReaders.Slot u)
    (f : (ActualRunQlocalNativeTuple.orbit D s.1).Mood) :
    let k := depth (D.choice s.1).2.1
    let δ := RG05Readout.Flatten.placeR (R.family.S.toDepth hn p) (D.choice s.1).1
    let r := ((R.family.S.toDepth hn p).count.val : ℝ)⁻¹
    ActualOriginalQReaders.readers Q D u μ orders s f = ∑ w : Word k,
      (ActualOriginalQReaders.fee Q u μ orders s * Motion.scalar (D.motion s.1)
        (ActualRunQlocalNativeTuple.constant D s.1 * multiplier (D.choice s.1).2.1 r w)) *
        jet k w (coordinates.symm δ) f.val := by
  intro k δ r
  change ActualOriginalQReaders.fee Q u μ orders s *
    QlocalSignedReadout.native _ _ _ _ _ δ r f = _
  rw [oriented, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc ..).symm)

/-- The curvature Haar color, geometric monomial and original Q coefficient
are all selected before the cutoff and the test. -/
def bareColor (s : ActualOriginalQPackets.Row (R := R) u)
    (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex) : ℂ :=
  NativeCurvatureTensor.coefficient (fun a => (word s.2.2.val a).2) j *
    (MvPolynomial.coeff s.2.2.val ((ofRun R ((ActualOriginalQPackets.degree u) s.1)).data.shape s.2.1) *
      ActualOriginalQReaders.coordinates (R := R) u s.1 s.2.1)

omit [DecidableEq V] [Fintype V] in
private theorem threshold (N : ℕ) (s : ActualOriginalQPackets.Row (R := R) u) :
    ActualRunKernelPackets.weight R (ActualOriginalQPackets.degree u) N p L s *
      ActualOriginalQReaders.scaledCoordinates (R := R) (p := p) (L := L) u N s.1 s.2.1 =
    MvPolynomial.coeff s.2.2.val ((ofRun R ((ActualOriginalQPackets.degree u) s.1)).data.shape s.2.1) *
      ActualOriginalQReaders.coordinates (R := R) u s.1 s.2.1 := by
  let t := (R.family.path.rep N p L).p.threshold
  let k := fieldRank R (ActualOriginalQPackets.degree u) s
  have ht : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (R.family.path.rep N p L).p.threshold_pos.ne'
  let mon := MvPolynomial.coeff s.2.2.val ((ofRun R ((ActualOriginalQPackets.degree u) s.1)).data.shape s.2.1)
  let src := ActualOriginalQReaders.coordinates (R:=R) u s.1 s.2.1
  change (((t⁻¹ ^ k : ℝ) : ℂ) * mon) * (((t^k : ℝ) : ℂ) * src) = mon*src
  simp only [Complex.ofReal_pow,Complex.ofReal_inv,inv_pow]
  calc
    _ = (((t : ℂ)^k)⁻¹*(t : ℂ)^k)*(mon*src) := by ac_rfl
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ ht), one_mul]

omit [DecidableEq V] [Fintype V] in
/-- Exact restoration in the original registered token, separately at every
color and independently given source. The stored Laurent power is retained
through the cancellation with the stored numerator on this one funded Run. -/
theorem primitive (N : ℕ) (hL : L ≤ N) (s : ActualOriginalQPackets.Row (R := R) u)
    (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s : ℤ)) *
      (ActualOriginalQPackets.token Q D u μ orders N s).gem j x =
    bareColor u s j * ActualOriginalQReaders.readers Q D u μ orders s.1 (x s.1.1) := by
  let z : ℂ := Pert.Asymptotics.regulatorRun R.family N p L
  let k := fieldRank R (ActualOriginalQPackets.degree u) s
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr (regulator_pos R N p L hL).ne'
  have hc : z^(-(k : ℤ)) * z^k = 1 := by rw [zpow_neg,zpow_natCast,inv_mul_cancel₀ (pow_ne_zero _ hz)]
  let H := NativeCurvatureTensor.coefficient (fun a => (word s.2.2.val a).2) j
  let f := ActualOriginalQReaders.readers Q D u μ orders s.1 (x s.1.1)
  let a := ActualRunKernelPackets.weight R (ActualOriginalQPackets.degree u) N p L s
  let b := ActualOriginalQReaders.scaledCoordinates (R := R) (p := p) (L := L) u N s.1 s.2.1
  change z^(-(k : ℤ))*(H*((z^k*a)*(f*b))) = _
  calc
    _ = (z^(-(k : ℤ))*z^k) * (H*(a*b)*f) := by ac_rfl
    _ = _ := by rw [hc,one_mul,show a*b=_ from threshold (p := p) (L := L) u N s]; rfl

omit [DecidableEq V] [Fintype V] in
/-- The complete addressed row after cancellation of its original Laurent and
threshold powers. Both sides retain the per-color complex coefficient. -/
theorem addressed (N : ℕ) (hL : L ≤ N) (s : ActualOriginalQPackets.Row (R := R) u)
    (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    let k := depth (D.choice s.1.1).2.1
    let δ := RG05Readout.Flatten.placeR (R.family.S.toDepth hn p) (D.choice s.1.1).1
    let r := ((R.family.S.toDepth hn p).count.val : ℝ)⁻¹
    (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s : ℤ)) *
      (ActualOriginalQPackets.token Q D u μ orders N s).gem j x = ∑ a : Word k,
      (bareColor u s j * (ActualOriginalQReaders.fee Q u μ orders s.1 * Motion.scalar (D.motion s.1.1)
        (ActualRunQlocalNativeTuple.constant D s.1.1 * multiplier (D.choice s.1.1).2.1 r a))) *
        jet k a (coordinates.symm δ) (x s.1.1).val := by
  intro k δ r
  rw [primitive Q D u μ orders N hL, original Q D u μ orders,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc ..).symm)

/-- Exact total variation of the addressed fixed-frame weights before external
tests, including an arbitrary complex source fee, original signed amplitude,
retained curvature coefficient, affine scale and genuine Taylor factorial. -/
theorem variation {d : ℕ} (i : Letter d) (t : Motion) (field fee amp : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (∑ a : Word (depth i), ‖field*(fee*Motion.scalar t (amp*multiplier i r a))‖) =
    ‖field‖*‖fee‖*‖amp‖*(r^depth i*((depth i).factorial : ℝ)⁻¹)*price (depth i) i.2 := by
  unfold price
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [multiplier,norm_mul,Motion.norm_scalar,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr _),abs_of_nonneg (by positivity : 0≤((depth i).factorial:ℝ)⁻¹)]
  ring

private theorem frame_pos (k : ℕ) : 0 < coordinateCost k := by
  have hn : coordinates.symm.toContinuousLinearMap ≠ 0 := by
    intro h
    have hz := congrArg (fun A : E4 →L[ℝ] Pos => (A (coordinates (fun _ => 1))) 0) h
    simp at hz
  exact mul_pos (mul_pos (write_cost k).choose_spec.1 (by positivity)) (pow_pos (norm_pos_iff.mpr hn) _)

/-- Fixed finite frame change paid by derivative degree, prior to all physical
requests, path rows and external tests. -/
def frameRate (k : ℕ) (b : Beam k) : ℝ := 1 + price k b / coordinateCost k

private theorem rate_covers (k : ℕ) (b : Beam k) {h : ℝ} (hh : 1 ≤ h) :
    ((k.factorial : ℝ)⁻¹)*price k b ≤ frameRate k b * (coordinateCost k*h) := by
  have hc := frame_pos k
  have hp : 0 ≤ price k b := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfac : 1 ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have he : price k b ≤ frameRate k b * coordinateCost k := by
    unfold frameRate
    rw [add_mul,one_mul,div_mul_cancel₀ _ hc.ne']
    linarith
  calc
    _ ≤ 1*price k b := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hfac) hp
    _ ≤ frameRate k b * coordinateCost k := by simpa using he
    _ ≤ frameRate k b * (coordinateCost k*h) := by rw [←mul_assoc]; exact le_mul_of_one_le_right (hp.trans he) hh

/-- The complete original field column at the formal numerator: its physical
fine coupling is frozen until the separate formal marked logarithm is built. -/
def fieldColumn (N : ℕ) (s : ActualOriginalQPackets.Row (R := R) u)
    (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex) : ℂ :=
  NativeCurvatureTensor.coefficient (fun i => (word s.2.2.val i).2) j *
    (((Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^fieldRank R (ActualOriginalQPackets.degree u) s *
      ActualRunKernelPackets.weight R (ActualOriginalQPackets.degree u) N p L s) *
      ActualOriginalQReaders.scaledCoordinates (R := R) (p := p) (L := L) u N s.1 s.2.1)

omit [DecidableEq V] [Fintype V] in
/-- Simultaneous total variation for every color and every independently
addressed source direction is covered by the actual stored coin on this row,
up to its preselected finite change of derivative coordinates. -/
theorem purchased (N : ℕ) (s : ActualOriginalQPackets.Row (R := R) u) :
    let i := (D.choice s.1.1).2.1
    let k := depth i
    let r := ((R.family.S.toDepth hn p).count.val : ℝ)⁻¹
    let c := ActualOriginalQReaders.fee Q u μ orders s.1
    let A := ActualRunQlocalNativeTuple.constant D s.1.1
    (∑ j, ∑ a : Word k, ‖fieldColumn (p := p) (L := L) u N s j *
      (c*Motion.scalar (D.motion s.1.1) (A*multiplier i r a))‖) ≤
      frameRate k i.2 * (ActualOriginalQPackets.token Q D u μ orders N s).coin := by
  intro i k r c A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let x := coordinates.symm (RG05Readout.Flatten.placeR (R.family.S.toDepth hn p) (D.choice s.1.1).1)
  let h := (ActualRunQlocalNativeTuple.orbit D s.1.1).height x
  have hh : 1 ≤ h := one_le_pow₀ (by linarith [norm_nonneg x] : 1 ≤ 1+‖x‖)
  have hf := rate_covers k i.2 hh
  let P := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^fieldRank R (ActualOriginalQPackets.degree u) s *
      ActualRunKernelPackets.weight R (ActualOriginalQPackets.degree u) N p L s
  let Z := ActualOriginalQReaders.scaledCoordinates (R := R) (p := p) (L := L) u N s.1 s.2.1
  let H := NativeCurvatureTensor.coefficient (fun a => (word s.2.2.val a).2)
  change _ ≤ frameRate k i.2 * ((∑ j, ‖H j‖) * (‖P‖*((‖c‖*(‖A‖*(r^k*(coordinateCost k*h))))*‖Z‖)))
  have each (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s)→G.ColorIndex) :
      (∑ a : Word k, ‖fieldColumn (p:=p) (L:=L) u N s j *
        (c*Motion.scalar (D.motion s.1.1) (A*multiplier i r a))‖)=
      ‖fieldColumn (p:=p) (L:=L) u N s j‖*‖c‖*‖A‖*(r^k*((k.factorial:ℝ)⁻¹))*price k i.2 :=
    variation i (D.motion s.1.1) _ c A r hr
  simp_rw [each]
  calc
    _ = (∑ j, ‖H j‖)*‖P‖*‖Z‖*‖c‖*‖A‖*r^k*(((k.factorial : ℝ)⁻¹)*price k i.2) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      change ‖H j*(P*Z)‖*‖c‖*‖A‖*(r^k*((k.factorial : ℝ)⁻¹))*price k i.2 = _
      simp only [norm_mul]; ring
    _ ≤ (∑ j, ‖H j‖)*‖P‖*‖Z‖*‖c‖*‖A‖*r^k*(frameRate k i.2*(coordinateCost k*h)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

/-- Every actual original startup packet is the concrete physically frozen
row of the prescribed finite list, with its original independent source mark.
The heterogeneous equality transports its exact path rank. -/
theorem frozen_selected (N i : ℕ)
    (T : Token G (R.family.side L p) (fun v => (ActualRunQlocalNativeTuple.orbit D v).Mood)
      ((ActualOriginalQFrozenInput.packets Q D u μ orders N).rank i))
    (hT : (ActualOriginalQFrozenInput.packets Q D u μ orders N).packet i = some T) :
    ∃ s : ActualOriginalQPackets.Row (R := R) u,
      (ActualOriginalQFrozenInput.packets Q D u μ orders N).mode i = (Stock.census V).fire s.1.1 ∧
      (ActualOriginalQFrozenInput.packets Q D u μ orders N).power i = 0 ∧
      HEq T (scaleToken ((Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^
        (-(fieldRank R (ActualOriginalQPackets.degree u) s : ℤ))) (ActualOriginalQPackets.token Q D u μ orders N s)) := by
  let P := ActualOriginalQPackets.packets Q D u μ orders N
  let g := Pert.Asymptotics.regulatorRun R.family N p L
  change (ActualPacketCouplingFreeze.freeze P g).packet i = some T at hT
  rw [ActualPacketCouplingFreeze.freeze_packet] at hT
  obtain ⟨t, ht, hv⟩ := Option.map_eq_some_iff.mp hT
  let prop := fun (v : (Stock.census V).Mode) (r : ℕ) (power : ℤ)
      (t' : Token G (R.family.side L p) (fun v => (ActualRunQlocalNativeTuple.orbit D v).Mood) r) =>
    ∃ s : ActualOriginalQPackets.Row (R := R) u, v = (Stock.census V).fire s.1.1 ∧
      HEq (scaleToken ((g : ℂ)^power) t')
        (scaleToken ((g : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s : ℤ)))
          (ActualOriginalQPackets.token Q D u μ orders N s))
  have hp : prop (P.mode i) (P.rank i) (P.power i) t := by
    let e := (Fintype.equivFin (ActualOriginalQPackets.Row (R := R) u)).symm
    exact MarkedPackets.ofFin_all (fun j => (Stock.census V).fire (e j).1.1)
      (fun j => tokenRank R (ActualOriginalQPackets.degree u) (e j))
      (fun j => -(fieldRank R (ActualOriginalQPackets.degree u) (e j) : ℤ))
      (fun j => ActualOriginalQPackets.token Q D u μ orders N (e j))
      (fun j => (Stock.census V).fire_hot (e j).1.1)
      (fun j => by have h := ActualRunKernelPackets.term_grade R (ActualOriginalQPackets.degree u) (e j); omega)
      prop (fun j => ⟨e j,rfl,HEq.rfl⟩) i t ht
  obtain ⟨s,hs,hv'⟩ := hp
  exact ⟨s,hs,rfl,hv ▸ hv'⟩

omit [DecidableEq V] [Fintype V] in
/-- The physically frozen numerator cancels its own stored grading at each
individual field colour and before every choice of test. The resulting bare
shape is independent of cutoff, period, and the stage threshold. -/
theorem frozen_field (N : ℕ) (hL : L ≤ N) (s : ActualOriginalQPackets.Row (R := R) u)
    (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex) :
    (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s : ℤ)) *
      fieldColumn (p:=p) (L:=L) u N s j = bareColor u s j := by
  let z : ℂ := Pert.Asymptotics.regulatorRun R.family N p L
  let k := fieldRank R (ActualOriginalQPackets.degree u) s
  let a := ActualRunKernelPackets.weight R (ActualOriginalQPackets.degree u) N p L s
  let b := ActualOriginalQReaders.scaledCoordinates (R := R) (p := p) (L := L) u N s.1 s.2.1
  let H := NativeCurvatureTensor.coefficient (fun h => (word s.2.2.val h).2) j
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr (regulator_pos R N p L hL).ne'
  have hc : z^(-(k : ℤ))*z^k = 1 := by rw [zpow_neg,zpow_natCast,inv_mul_cancel₀ (pow_ne_zero _ hz)]
  change z^(-(k : ℤ))*(H*((z^k*a)*b)) = _
  calc
    _ = (z^(-(k : ℤ))*z^k)*(H*(a*b)) := by ac_rfl
    _ = _ := by rw [hc,one_mul,show a*b=_ from threshold (p:=p) (L:=L) u N s]; rfl

omit [DecidableEq V] [Fintype V] in
/-- The addressed joint colour/coordinate variation is bought by the exact
frozen token that the original analytic startup actually supplies. -/
theorem frozen_purchased (N : ℕ) (hL : L ≤ N) (s : ActualOriginalQPackets.Row (R := R) u) :
    let i := (D.choice s.1.1).2.1
    let k := depth i
    let r := ((R.family.S.toDepth hn p).count.val : ℝ)⁻¹
    let c := ActualOriginalQReaders.fee Q u μ orders s.1
    let A := ActualRunQlocalNativeTuple.constant D s.1.1
    let z := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s : ℤ))
    (∑ j, ∑ a : Word k, ‖bareColor u s j*(c*Motion.scalar (D.motion s.1.1) (A*multiplier i r a))‖) ≤
      frameRate k i.2*(scaleToken z (ActualOriginalQPackets.token Q D u μ orders N s)).coin := by
  intro i k r c A z
  have h := mul_le_mul_of_nonneg_left (purchased Q D u μ orders N s) (norm_nonneg z)
  change _ ≤ frameRate k i.2*(‖z‖*(ActualOriginalQPackets.token Q D u μ orders N s).coin)
  calc
    _ = ‖z‖*(∑ j, ∑ a : Word k, ‖fieldColumn (p:=p) (L:=L) u N s j*
          (c*Motion.scalar (D.motion s.1.1) (A*multiplier i r a))‖) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun a _ => ?_))
      rw [←frozen_field (p:=p) (L:=L) u N hL s j,mul_assoc,norm_mul]
    _ ≤ _ := h.trans_eq (by ring)

end YM.Integration.OriginalSourceJetAddresses
end
