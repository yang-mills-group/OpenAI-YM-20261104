import YM.RG11Proof.Fields.Tests
import YM.RG11Proof.Jets.Law
import YM.Pert.Position.Frame
import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis
/-!
# Use a real basis of actual free `E` through a horizon

Then the permitted constant-basis shifts already given by `Position.Buffer`
have (order-by-order) real row matrices, and define one `Constraints` on
that horizon. No need to quotient a second time by an uncharacterized ENorm;
E is already the quotient and finite bases must be independent there. Keep
`Position.RawLabels`/stencil representatives for any evaluations including
near contacts; no interacting or BRST quotient theorem here.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD
open scoped Classical BigOperators

variable {G : Gauge} {F : Frames G} {d:ℕ}

structure Basis (F : Frames G) (d : ℕ) where
  m : ℕ
  b : Module.Basis (Fin (m+1)) ℂ (E F d)
  unitIndex : Fin (m+1)
  unitAt : b unitIndex=(freeTable F).unit d
  pinned (i : Fin (m+1)) : (freeTable F).conj (table_spin F) d (b i)=b i

/-- One supplied real finite basis for every finite free horizon. Not yet a
CHOICE WITH RESTRICTION consistency. -/
def atStage (F : Frames G) (d : ℕ) : Basis F d :=
  ⟨(recorded F d).m,(recorded F d).b,0,(recorded F d).unit_,(recorded F d).real_i⟩

namespace Basis
abbrev J (B : Basis F d) := Fin (B.m+1)

variable (B : Basis F d)

def put (B : Basis F d) (x : J B→ℝ) : E F d := B.b.equivFun.symm fun i=> (x i:ℂ)

theorem put_sum (x:J B →ℝ) : B.put x=∑ i,(x i:ℂ) • B.b i := Module.Basis.equivFun_symm_apply ..

theorem coeff_put (x : J B→ℝ) (i) : B.b.equivFun (B.put x) i=(x i:ℂ):= congrFun (B.b.equivFun.apply_symm_apply _) i

theorem put_injective : Function.Injective B.put:=fun _ _ h=>funext fun i=> Complex.ofReal_injective (by rw [← B.coeff_put,← B.coeff_put,h])
@[simp] theorem put_zero : B.put 0=0:= by rw [put_sum]; simp

/-- Simple reality patch. -/
def overReals (v : E F d) := (freeTable F).conj (table_spin F) d v=v

theorem puts_real (x : J B→ℝ):overReals (B.put x):=by unfold overReals; rw [put_sum,map_sum]; simp only [map_smulₛₗ, B.pinned]; congr! 2; first|rfl|simp

theorem same_bar (v : E F d) (i : J B) : B.b.equivFun ((freeTable F).conj (table_spin F) d v) i = star (B.b.equivFun v i) := by
  conv_lhs=>rw [← B.b.sum_equivFun v,map_sum]
  simp_rw [map_smulₛₗ,B.pinned,map_sum,map_smul,Finset.sum_apply]
  simp_rw [Pi.smul_apply, Module.Basis.equivFun_self]
  classical
  simp only [smul_eq_mul, mul_ite,mul_one,mul_zero]
  rw [Finset.sum_eq_single i] <;> simp_all

def coord (v : E F d) (i : J B) := (B.b.equivFun v i).re

theorem coord_real {v : E F d} (hv : overReals v) (i : J B): (B.coord v i:ℂ)=B.b.equivFun v i:= by
  have h := B.same_bar v i; rw [hv] at h
  have he : (B.b.equivFun v i).im = -(B.b.equivFun v i).im:= congrArg Complex.im h
  have hv : (B.b.equivFun v i).im=0:=by linarith [he]
  apply Complex.ext
  · rfl
  exact hv.symm

theorem put_round (v : E F d) (hv : overReals v) : B.put (B.coord v) = v:= by
  unfold put; simp only [coord_real B hv]; exact B.b.equivFun.symm_apply_apply _

-- Compatible matrix action on ALL of E (complex-linear). Produces a Buffer
-- only on the indicated Constraints below.
def liftRows (K : Square (J B) ℝ):Module.End ℂ (E F d) :=
  (B.b.equivFun.symm.toLinearMap).comp <| ((rowLin K).comp B.b.equivFun.toLinearMap)
where rowLin (K:Square (J B) ℝ):(J B→ℂ)→ₗ[ℂ](J B→ℂ):=LinearMap.pi fun i=>∑ j:J B,(K j i:ℂ) • (LinearMap.proj (R:=ℂ) j)

theorem read_row (K : Square (J B) ℝ) (v : E F d) (i : J B): B.b.equivFun (B.liftRows K v) i=
    ∑ j,B.b.equivFun v j*(K j i:ℂ) := by
  unfold liftRows; rw [LinearMap.comp_apply, LinearEquiv.coe_coe,B.b.equivFun.apply_symm_apply]; unfold liftRows.rowLin; simp [mul_comm]

theorem row_basis (K : Square (J B) ℝ) (i:J B): B.liftRows K (B.b i) = B.put (fun j=>K i j):=by
  apply B.b.equivFun.injective; ext1 j
  rw [read_row,B.coeff_put]; simp only [Module.Basis.equivFun_self]
  simp [ite_mul]

theorem row_map_zero : B.liftRows 0=0:= by apply B.b.ext; intro i; rw [row_basis]; exact B.put_zero

theorem row_map_add (K W:Square (J B) ℝ) : B.liftRows (K+W)=B.liftRows K+B.liftRows W:=by
  apply B.b.ext; intro i; simp_rw [LinearMap.add_apply,row_basis,Matrix.add_apply,put_sum,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]

theorem row_map_smul (r:ℝ)(W:Square (J B) ℝ): B.liftRows (r • W)=(r:ℂ) • B.liftRows W:=by
  apply B.b.ext; intro i
  simp_rw [LinearMap.smul_apply,row_basis,put_sum,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul,Finset.smul_sum, smul_smul]

-- reversed order (row convention).
theorem row_map_mul (K W:Square (J B) ℝ): B.liftRows (K*W)= (B.liftRows W).comp (B.liftRows K):=by
  apply B.b.ext; intro i
  apply B.b.equivFun.injective; ext1 j
  simp_rw [LinearMap.comp_apply,row_basis] -- may tries too much
  rw [read_row]
  simp_rw [coeff_put]; rw [Matrix.mul_apply, Complex.ofReal_sum]; simp

theorem row_injective : Injective B.liftRows:=by intro x y h; ext i j; have he:=LinearMap.congr_fun h (B.b i); rw [B.row_basis, B.row_basis] at he; exact congrFun (B.put_injective he) j

def realLift (K:Square (J B) ℝ) : E F d →L[ℝ] E F d := ((B.liftRows K).restrictScalars ℝ).toContinuousLinearMap

def certified (K:Square (J B) ℝ):Prop:= B.realLift K ∈ buffers F d

/-- The constraint ledger for later use; we use this rather than postulating
consistency of any scheme frame with null stencils. -/
def guard (B : Basis F d) : Constraints ℝ (J B) where
  vary := {
    carrier := {K | B.certified K}
    zero_mem' := by
      change B.realLift 0 ∈ buffers F d
      have he : B.realLift 0=0:= ContinuousLinearMap.ext fun v=>by rw [realLift,row_map_zero]; rfl
      rw [he]; exact Submodule.zero_mem _
    add_mem' := by
      intro x y (h : B.certified x) (j:B.certified y)
      have he:B.realLift (x+y)= B.realLift x+B.realLift y:= ContinuousLinearMap.ext fun v=>by rw [realLift,row_map_add]; exact (LinearMap.add_apply (B.liftRows x) (B.liftRows y) v)
      change B.realLift (x+y)∈ buffers F d; rw [show B.realLift (x+y)= B.realLift x+B.realLift y from he]
      exact Submodule.add_mem _ h j
    smul_mem' := by
      intro c x (h : B.certified x)
      change B.realLift (c • x)∈buffers F d
      rw [show B.realLift (c • x)=c • B.realLift x from ContinuousLinearMap.ext fun v=>?_]
      · exact Submodule.smul_mem _ c h
      change B.liftRows (c • x) v=c • B.liftRows x v; rw [row_map_smul, LinearMap.smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl }
  both {x y} h j := by
    change B.certified (x*y); unfold certified
    change B.certified x at h; change B.certified y at j
    let D:= B.realLift x; let L := B.realLift y
    rw [show B.realLift (x*y)= L.comp D from ContinuousLinearMap.ext fun i=> by rw [realLift,row_map_mul]; rfl]
    obtain ⟨hu,hL,hb,hH,hc⟩:=h; obtain ⟨ju,jL,jb,jH,jc⟩:=j
    constructor
    · change L (B.realLift x _) = _; rw [hu,map_zero]
    exact ⟨fun e he p H=> jL e he _ (hL e he _ H), fun p=> (jb (D p)).trans (congrArg (fun v=>L v) (hb p)),fun s p=>(jH s (D p)).trans (congrArg (fun v=> L v) (hH s p)),fun p=> (congrArg (fun v=>L v) (hc p)).trans (jc (D p))⟩ -- args

def operates (B:Basis F d) (z:B.guard.vary): Buffer F d:=⟨B.realLift z.val,z.property⟩

theorem shift_reads (z:B.guard.vary) (i): (B.operates z).val (B.b i)=∑ j:J B,(z.val i j:ℂ) • B.b j := (row_basis ..).trans (put_sum ..)

theorem operates_inj : Injective B.operates := by
  intro x y h; apply Subtype.ext; apply B.row_injective; apply LinearMap.ext; intro v
  exact congrArg (fun z : Buffer F d=> z.val v) h
end Basis
end YM.RG11.Fields
