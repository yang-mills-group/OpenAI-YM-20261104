import YM.Integration.WilsonPublicForkGeometry

/-! Relative housing, exact dimensions and the cutoff-free logarithmic tariff
of the original finite near roster and its single physical exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkRooms
open Finset Function Set Table OPE OPE.Arboreal OPE.Log WilsonPublicForkGeometry
open WilsonPublicForkGeometry.Node
open scoped Topology BigOperators Classical
variable {I:Type} [Fintype I]
theorem names (u:↥(near I)):∃i,u.1=leaf i:=by
  obtain ⟨i,_,e⟩:=Finset.mem_map.mp u.2; exact ⟨i,e.symm⟩
def nearSeat : I≃↥(near I):=Equiv.ofBijective (fun i=>(⟨leaf i,near_mem i⟩:↥(near I))) ⟨by
  intro i j eq;exact leaf.inj (congrArg Subtype.val eq),by
  intro u;obtain ⟨i,hi⟩:=names u;exact ⟨i,Subtype.ext hi.symm⟩⟩

theorem inner {r t M δ:ℝ}{x:I→E4}{z:E4}(rp:0<r)
    (cl:∀i,‖x i‖≤M)(sep:∀i j,i≠j→δ≤‖x i-x j‖) :
    WithinRoom r M δ (crop (WilsonPublicForkGeometry.position r t x z) (near I)) 0 := by
  constructor
  · intro u
    obtain ⟨i,hi⟩:=names u
    change ‖WilsonPublicForkGeometry.position r t x z u.val-0‖≤M*r
    rw [hi,sub_zero];change ‖r • x i‖≤M*r
    rw [norm_smul,Real.norm_of_nonneg rp.le,mul_comm];gcongr;exact cl i
  · intro u v ne
    obtain ⟨i,hi⟩:=names u
    obtain ⟨j,hj⟩:=names v
    change δ*r≤‖WilsonPublicForkGeometry.position r t x z u.val-WilsonPublicForkGeometry.position r t x z v.val‖
    rw [hi,hj];change δ*r≤‖r • x i-r • x j‖
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (sep i j (fun e=>ne (Subtype.ext (hi.trans ((congrArg leaf e).trans hj.symm))))) rp.le

omit [Fintype I] in
theorem outside {r t M δ:ℝ}{x:I→E4}{z:E4}(tp:0<t) (mn:0≤M)
    (nz:‖z‖≤M)(away:δ≤‖z‖) : WithinRoom t M δ (crop (WilsonPublicForkGeometry.position r t x z) (outer I)) 0 := by
  constructor
  · rintro ⟨i,hi⟩
    rcases (by simpa [outer] using hi : i=child ∨ i=far) with rfl|rfl
    · change ‖(0:E4)-0‖≤M*t;simpa using mul_nonneg mn tp.le
    · change ‖t • z-0‖≤M*t;rw [sub_zero,norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ ne
    have under:δ*t≤‖t • z‖:=by rw [norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr
    rcases (by simpa [outer] using hi : i=child ∨ i=far) with rfl|rfl <;>
      rcases (by simpa [outer] using hj : j=child ∨ j=far) with rfl|rfl
    · exact (ne rfl).elim
    · change _≤‖0-t • z‖;simpa using under
    · change _≤‖t • z-0‖;simpa using under
    · exact (ne rfl).elim

variable {G:Gauge}{L:Register G}
def load (p:Node I→L.Token):ℕ := ∑i,(p (leaf i)).1
def mass (p:Node I→L.Token)(r t:ℝ):ℝ := r^(load p)*t^(p far).1

theorem innerdeg (p:Node I→L.Token):sigma (crop p (near I))=load p:=by
  rw [sigma_set];simp [near,load]
theorem outerdeg (p:Node I→L.Token)(a:L.Token):sigma (crop (update p child a) (outer I))=a.1+(p far).1:=by
  rw [sigma_set];simp [outer]
theorem fee (p:Node I→L.Token)(r t:ℝ)(n:ℕ):
    (frame I).fee p (radius r t) (frame I).leaves (frame I).root n=mass p r t/t^n:=by
  rw [Arboreal.fee,Arboreal.rent,WilsonPublicForkGeometry.leaves]
  simp [mass,load,near,frame,radius,Finset.prod_pow_eq_pow_sum,mul_comm]
omit [Fintype I] in
theorem prestige (r t:ℝ): Arboreal.prestige (frame I) (radius r t)=(1+run t)*(1+run r):=by
  simp [Arboreal.prestige,frame,radius]
omit [Fintype I] in
theorem ratio (r t:ℝ):(frame I).ratioAt (radius r t) child=r/t:=rfl
end YM.Integration.WilsonPublicForkRooms
