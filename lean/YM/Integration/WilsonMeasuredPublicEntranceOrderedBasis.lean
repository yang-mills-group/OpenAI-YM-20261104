import YM.Integration.WilsonThermometerUnitFilingFourSquare
/-! The two original regulator limits of the finite Wilson forms on a bounded set of physical input labels. The intermediate form really is the fixed-period ultraviolet limit. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOrderedBasis
open Filter Function Set Finset Extraction Table Spec Next.UVStress
open private finiteMoment finiteMoment_eq from YM.Next.UV_STRESS.Vary
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{order:Extraction.Order}{S:Table C.book}
  (F:Final C order S){n:ℕ}(d:Caps n)(φ:Test n)
local notation "E" => fun i:Fin n=>C.label (d i)
local notation "Keys" => Code (fun i:Fin n=>C.label (d i))

def finiteValue (N p:ℕ)(y:C.book.Vector d):ℂ:=
  Order.smears C N p (fun i=>⟨d i,y i⟩) φ

def publicValue (y:C.book.Vector d):ℂ:=
  φ.applyTo fun x=>S.classMoment S d x (fun i=>S.project (d i) (y i))

def form (v:Keys→ℂ)(y:C.book.Vector d):ℂ:=∑a,coords (E) a y*v a

def scale (H:Fin n→ℝ)(a:Keys):ℝ:=
  ∏i,‖((Module.finBasis ℂ ((E) i)).coord (a i)).toContinuousLinearMap‖*H i

def debt (H:Fin n→ℝ)(u v:Keys→ℂ):ℝ:=
  ∑a,scale (C:=C) d H a*‖u a-v a‖

include F in
theorem represented (y:C.book.Vector d):
    S.integralOn d y φ=publicValue (S:=S) d φ y:=by
  apply φ.apply_eq
  intro x hx
  exact (S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) d hx y).symm

theorem finite_form (N p:ℕ)(y:C.book.Vector d):
    finiteValue d φ N p y=form d (fun a=>finiteValue d φ N p (combination (E) a)) y:=by
  unfold finiteValue form
  simp_rw [finiteMoment_eq]
  exact basis_tuple (E) y (finiteMoment C N p d φ)

include F in
theorem public_form (y:C.book.Vector d):
    publicValue (S:=S) d φ y=form d (fun a=>publicValue (S:=S) d φ (combination (E) a)) y:=by
  have read(x:C.book.Vector d):Tendsto (fun z:ℕ×ℕ=>finiteValue d φ z.1 z.2 x) order.fuse
      (𝓝 (publicValue (S:=S) d φ x)):=by
    rw [←represented F d φ x]
    exact calibrated_smear (d:=d) F.room.ordered order.fuse le_rfl φ
      (v:=fun _=>x) (x:=x) (fun i=>tendsto_const_nhds)
  have assembled:Tendsto (fun z:ℕ×ℕ=>form d (fun a=>finiteValue d φ z.1 z.2 (combination (E) a)) y)
      order.fuse (𝓝 (form d (fun a=>publicValue (S:=S) d φ (combination (E) a)) y)):=
    tendsto_finsetSum _ (fun a _=>(read (combination (E) a)).const_mul _)
  apply tendsto_nhds_unique (read y)
  exact assembled.congr' (.of_forall fun z=>(finite_form d φ z.1 z.2 y).symm)

theorem cost (H:Fin n→ℝ)(a:Keys){y:C.book.Vector d}(bounded:∀i,‖y i‖≤H i):
    ‖coords (E) a y‖ ≤ scale (C:=C) d H a:=by
  unfold coords scale
  rw [norm_prod]
  apply prod_le_prod (fun _ _=>norm_nonneg _)
  intro i _
  let m:=((Module.finBasis ℂ ((E) i)).coord (a i)).toContinuousLinearMap
  exact (m.le_opNorm (y i)).trans (mul_le_mul_of_nonneg_left (bounded i) (norm_nonneg _))

theorem compare (H:Fin n→ℝ)(u v:Keys→ℂ){y:C.book.Vector d}(bounded:∀i,‖y i‖≤H i):
    ‖form d u y-form d v y‖≤debt (C:=C) d H u v:=by
  unfold form debt
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_right (cost d H a bounded) (norm_nonneg _)

theorem clears {ι:Type*}{f:Filter ι}(H:Fin n→ℝ)(values:ι→Keys→ℂ)(target:Keys→ℂ)
    (reads:∀a,Tendsto (fun i=>values i a) f (𝓝 (target a))):
    Tendsto (fun i=>debt (C:=C) d H (values i) target) f (𝓝 0):=by
  simpa only [debt,sub_self,norm_zero,mul_zero,Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ:Finset Keys) (fun a _=>
      (((reads a).sub (tendsto_const_nhds (x:=target a))).norm).const_mul (scale (C:=C) d H a))

/-- All upper and lower bounds use the same measured intermediate period form. -/
structure Release (H:Fin n→ℝ) where
  period:ℕ→Keys→ℂ
  ultraviolet:ℕ→ℕ→ℝ
  volume:ℕ→ℝ
  suitable:∀ᶠk in atTop,Extraction.suitable C.S (order.per k) φ
  first:∀p,Extraction.suitable C.S p φ →
    Tendsto (fun j=>ultraviolet (order.mesh j) p) atTop (𝓝 0)
  second:Tendsto (fun k=>volume (order.per k)) atTop (𝓝 0)
  fine:∀N p (y:C.book.Vector d),(∀i,‖y i‖≤H i) →
    ‖finiteValue d φ N p y-form d (period p) y‖≤ultraviolet N p
  outer:∀p (y:C.book.Vector d),(∀i,‖y i‖≤H i) →
    ‖form d (period p) y-publicValue (S:=S) d φ y‖≤volume p

include F in
theorem original (H:Fin n→ℝ):Nonempty (Release (C:=C) (order:=order) (S:=S) d φ H):=by
  have bought(a:Keys):order.limits (fun p=>Extraction.suitable C.S p φ)
      (fun N p=>finiteValue d φ N p (combination (E) a))
      (publicValue (S:=S) d φ (combination (E) a)):=by
    rw [←represented F]
    exact F.room.ordered.reads n (fun i=>⟨d i,combination (E) a i⟩) φ
  choose price upper lower using fun a=>(bought a).2
  let target:=fun a=>publicValue (S:=S) d φ (combination (E) a)
  let heard:=fun N p a=>finiteValue d φ N p (combination (E) a)
  let period:=fun p a=>price a p
  refine ⟨⟨period,(fun N p=>debt (C:=C) d H (heard N p) (period p)),
    (fun p=>debt (C:=C) d H (period p) target),?_,?_,?_,?_,?_⟩⟩
  · exact (F.room.ordered.reads n (fun i=>⟨d i,0⟩) φ).1
  · intro p room
    exact clears d H (fun j=>heard (order.mesh j) p) (period p) (fun a=>upper a p room)
  · exact clears d H (fun k=>period (order.per k)) target lower
  · intro N p y bounded
    rw [finite_form d φ N p y]
    exact compare d H _ _ bounded
  · intro p y bounded
    rw [public_form F d φ y]
    exact compare d H _ _ bounded

end YM.Integration.WilsonMeasuredPublicEntranceOrderedBasis
end
