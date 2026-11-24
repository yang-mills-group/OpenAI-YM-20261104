import YM.Integration.WilsonRootedMayerColumn
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSample

/-! Comparison of the intrinsic window mean and full normal-equation solution at a held
    physical field, including the genuine original planted rough flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineCenter
open Function Finset Lattice Wilson RG Pressure Pressure.Tube Tree Matrix
open Push Push.AbsoluteSums Precision SectorMeasure Oriented PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Coat Control Window Census Blaze Matter Greenbelt
open scoped BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}
    {P:Teller G}{W s μ C:ℝ}{Q:ConnectedActivityE6.Target G P}{o:Target.Order G W}{R:Rep G f}

/-- The full inverse has the same genuine linear load and the same field-dependent
    normal matrix as the held physical window. -/
abbrev full (X:Coat T F) := -((X.plate⁻¹).transpose *ᵥ X.linearBill)

lemma normal (X:Coat T F) {η r q v:ℝ} (h:Rotator P L η r q v X):
    X.plate *ᵥ full X + X.linearBill=0:=by
  have hs:(X.plate⁻¹).transpose=X.plate⁻¹:=by
    ext i k
    simpa only [IsHermitian,conjTranspose_apply,transpose_apply,star_trivial] using X.balanced.inv.apply i k
  rw [full,hs,Matrix.mulVec_neg, Matrix.mulVec_mulVec,h.scale.initial.1,Matrix.one_mulVec,neg_add_cancel]

/-- Recover the true unwindowed mean from the measured mean, using the native
    resolvent half-margin. Each estimate is independent of the number of bonds. -/
theorem field (X:Coat T F) {η r q v A:ℝ} (h:Rotator P L η r q v X)
    (hA:0≤A)(cap:∀e,‖X.μ e‖≤A):
    let δ:=distPay η r q (tubularPrice G L) X.B
    ‖full X‖≤2*A ∧ (∀i,|X.driftM i-full X i|≤2*(q*δ)*A) ∧
      ∀e,‖X.μ e-erect G (full X) e‖≤(Fintype.card G.ColorIndex:ℝ)*(2*(q*δ)*A):=by
  intro δ
  have hd:0≤δ:=mul_nonneg h.scale.disc (h.scale.heap _)
  have price:=h.scale.breach X.shutter
  have half:δ*q≤1/2:=calc
    δ*q≤(q⁻¹/2)*q:=mul_le_mul_of_nonneg_right h.cap h.scale.fuel.le
    _=1/2:=by field_simp [h.scale.fuel.ne']
  have rect:=normal X h
  have lin (i:Tubular f G):|X.linearBill i|≤q*‖full X‖:=by
    have eqn: (X.plate *ᵥ full X) i+X.linearBill i=0:=congrFun rect i
    rw [show X.linearBill i= -(X.plate *ᵥ full X) i from by linarith only [eqn],abs_neg]
    exact invoice h.scale.price h.full.hot.le i _ (fun j=>by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (full X) j)
      (norm_nonneg _)
  have gap:X.driftM-full X= -((X.kernelA-X.plate⁻¹).transpose *ᵥ X.linearBill):=by
    rw [Coat.driftM,full,Matrix.transpose_sub,Matrix.sub_mulVec]
    abel
  have error (i:Tubular f G):|X.driftM i-full X i|≤δ*(q*‖full X‖):=by
    change |(X.driftM-full X) i|≤_
    rw [gap,Pi.neg_apply,abs_neg]
    exact invoice price.2 h.scale.weather.1.le i _ lin (mul_nonneg h.scale.fuel.le (norm_nonneg _))
  have observed (i:Tubular f G):|X.driftM i|≤A:=(stand_cap i.2 (X.μ i.1)).trans (cap i.1)
  have bound:‖full X‖≤A+(1/2)*‖full X‖:=by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg hA (mul_nonneg (by norm_num) (norm_nonneg _)))).mpr
    intro i
    rw [Real.norm_eq_abs]
    calc
      |full X i|=|X.driftM i-(X.driftM i-full X i)|:=by ring_nf
      _≤|X.driftM i|+|X.driftM i-full X i|:=abs_sub ..
      _≤A+((δ*q)*‖full X‖):=by simpa only [mul_assoc] using add_le_add (observed i) (error i)
      _≤A+(1/2)*‖full X‖:=add_le_add_right (mul_le_mul_of_nonneg_right half (norm_nonneg _)) _
  have size:‖full X‖≤2*A:=by linarith only [bound]
  have fee (i:Tubular f G):|X.driftM i-full X i|≤2*(q*δ)*A:=calc
    _≤δ*(q*‖full X‖):=error i
    _≤δ*(q*(2*A)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left size h.scale.fuel.le) hd
    _=2*(q*δ)*A:=by ring
  refine ⟨size,fee,fun e=>?_⟩
  exact color_cover (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg h.scale.fuel.le hd)) hA)
    _ (fun j=>fee (e,j))

/-- The actual enrolled local factor carries a globally manifest coat even when
    its protected component is healthy and exterior plaquettes are flagged. -/
def held (T:Tube G S) (s K:ℝ) (χ:Chi) (V:Config G c) (p:Molecule S)
    (i:Greenbelt.Reserve S) (tag:S.Choices) (y:(Greenbelt.allot i).Slice G):Coat T (Greenbelt.allot i):=
  ((planted (prism T s χ K V (allot i)) p).taggedL tag).wrapY y

theorem original (H:Cash W s μ L Q o C T R) (χ:Chi) (V:Config G c) (p:Molecule S)
    (i:Greenbelt.Reserve S) (tag:S.Choices) (y:(Greenbelt.allot i).Slice G):
    let X:=held T s o.K χ V p i tag y
    let δ:=distPay o.eta o.gap o.ample (tubularPrice G L) X.B
    X.manifest ∧ X.plate *ᵥ full X + X.linearBill=0 ∧ ‖full X‖≤2*(o.cap*X.t) ∧
    (∀k,|X.driftM k-full X k|≤2*(o.ample*δ)*(o.cap*X.t)) ∧
      ∀e,‖X.μ e-erect G (full X) e‖≤(Fintype.card G.ColorIndex:ℝ)*(2*(o.ample*δ)*(o.cap*X.t)):=by
  intro X δ
  have hm:X.manifest:=planted_valid _ _
  have sails:Rotator P L o.eta o.gap o.ample o.indexPay X:=(H.laws.data.localP _ X rfl rfl hm).sails
  have cap:= (H.laws.data.safety.2.2.2 _ X rfl rfl hm).1
  exact ⟨hm,normal X sails,field X sails (mul_nonneg H.laws.data.safety.1.le sails.room.fiery.le) cap⟩

end YM.Integration.WilsonRootedHeldAffineCenter
