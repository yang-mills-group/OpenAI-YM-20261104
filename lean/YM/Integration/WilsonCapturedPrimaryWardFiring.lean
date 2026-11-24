import YM.MergeProof.Accent

/-! Change units separately on each original squarefree marker. A product retains
the common mode on every disjoint merge and the vacuum coefficient is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardFiring
open Function Finset Marker MergeProof.Accent Push.GridApprox.Nil
open scoped Classical BigOperators
variable {V:Type*} [DecidableEq V] (J:Census V) (b:V→ℝ)

def paint (p:Poly J) : Poly J := Poly.inject (fun s=>(Poly.toll b s:ℂ)*p.part s)

@[simp] theorem part (p:Poly J) (s:J.Mode):
    (paint J b p).part s=(Poly.toll b s:ℂ)*p.part s:=rfl

theorem send (s:J.Mode) (v:ℂ):paint J b (Poly.send s v)=Poly.send s ((Poly.toll b s:ℂ)*v):=by
  ext m
  by_cases h:m=s
  · subst m; simp [Poly.part_send]
  · simp [Poly.part_send,h]

private theorem multiply (p q:Poly J) : paint J b (p*q)=paint J b p*paint J b q := by
  ext s
  simp only [part,Poly.part_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h:Poly.merges x y s
  · simp only [if_pos h]
    have tariff:Poly.toll b s=Poly.toll b x*Poly.toll b y:=by
      unfold Poly.toll
      rw [←h.2,Finset.prod_union h.1]
    rw [tariff,Complex.ofReal_mul]
    ring
  · simp [h]

def names : Poly J →ₐ[ℂ] Poly J where
  toFun:=paint J b
  map_zero':=by ext s;simp [Poly.part_nil]
  map_one':=by change paint J b (Poly.send J.quiet 1)=Poly.send J.quiet 1;rw [send];simp
  map_add' p q:=by ext s;simp [Poly.part_plus,mul_add]
  map_mul':=multiply J b
  commutes' z:=by change paint J b (Poly.send J.quiet z)=Poly.send J.quiet z;rw [send];simp

@[simp] theorem names_part (p:Poly J) (s:J.Mode):
    (names J b p).part s=(Poly.toll b s:ℂ)*p.part s:=rfl

@[simp] theorem names_send (s:J.Mode) (a:ℂ):
    names J b (Poly.send s a)=Poly.send s ((Poly.toll b s:ℂ)*a):=send J b s a

@[simp] theorem names_bead (a:ℂ):names J b (Poly.bead J a)=Poly.bead J a:=(names J b).commutes a

variable [Fintype V]

theorem passing (p:Poly J):names J b (Poly.pass p)=Poly.pass (names J b p):=by
  simp [Poly.pass,map_sum,map_pow]

theorem signal (f:V→ℂ):names J b (Mach J f)=Mach J (fun i=>(b i:ℂ)*f i):=by
  simp [Mach]

omit [Fintype V] in
theorem toll (hb:∀i,0<b i) (w:V→ℝ) (s:J.Mode):
    Poly.toll (fun i=>w i/b i) s * Poly.toll b s=Poly.toll w s:=by
  unfold Poly.toll
  rw [←Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _=>div_mul_cancel₀ (w i) (hb i).ne'

end YM.Integration.WilsonCapturedPrimaryWardFiring
