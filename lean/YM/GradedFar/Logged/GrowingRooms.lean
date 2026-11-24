import YM.GradedFar.Logged.GrowingGeometry
import YM.OPE.Logarithmic
/-!
# Growing rooms & the exterior renormalizations on exactly these joints
Further adaptations of `WilsonPublicForkRooms`. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Tree
open Function Finset Filter Set OPE OPE.Arboreal OPE.Log
open scoped Topology BigOperators Classical
open Node
variable {I J:Type}[Fintype I][Fintype J]

lemma names (x:↥(near I J)): ∃ i,x.val=leaf i := by obtain ⟨i,_,hi⟩:= Finset.mem_map.mp x.property; exact ⟨i,hi.symm⟩
lemma names_far {j:Node I J}(h:j∈terminalS I J): ∃ i,j=far i := by obtain ⟨i,_,hi⟩:= Finset.mem_map.mp h; exact ⟨i,hi.symm⟩

theorem inner {r t M δ:ℝ}{x:I→E4}{z:J→E4}(o:E4)(rp:0<r)
    (cl:∀i,‖x i‖≤M)(sep:∀i j,i≠j→δ≤‖x i-x j‖) :
    WithinRoom r M δ (crop (position r t x z o) (near I J)) o := by
  constructor
  · intro u
    obtain ⟨i,hi⟩:=names u
    change ‖position r t x z o u.val-o‖≤M*r
    rw [hi, position,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg rp.le,mul_comm];gcongr;exact cl i
  intro u v ne
  obtain ⟨i,hi⟩:=names u
  obtain ⟨j,hj⟩:=names v
  change δ*r≤‖position r t x z o u.val-position r t x z o v.val‖
  rw [hi,hj];change δ*r≤‖o+r • x i-(o+r • x j)‖
  rw [add_sub_add_left_eq_sub,←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
  exact mul_le_mul_of_nonneg_left (sep i j (fun e=>ne (Subtype.ext (hi.trans ((congrArg leaf e).trans hj.symm))))) rp.le

theorem outside {r t M δ:ℝ}{x:I→E4}{z:J→E4}(o:E4)(tp:0<t) (mn:0≤M)
    (nz:∀ i,‖z i‖≤M)(away:∀ i,δ≤‖z i‖)(sep:∀ i j,i≠j→δ≤‖z i-z j‖) : WithinRoom t M δ (crop (position r t x z o) (outer I J)) o := by
  have he {i} (h:i∈outer I J) : i=child ∨ ∃j, i=far j := (Finset.mem_insert.mp h).imp_right names_far
  constructor
  · rintro ⟨i,hi⟩
    rcases he hi with rfl|⟨i,rfl⟩
    · change ‖o-o‖≤M*t;simpa using mul_nonneg mn tp.le
    change ‖o+t • z i-o‖≤M*t;rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr; exact nz i
  rintro ⟨i,hi⟩ ⟨j,hj⟩ ne
  have under i:δ*t≤‖t • z i‖:=by rw [norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr; exact away i
  rcases he hi with rfl|⟨i,rfl⟩ <;> rcases he hj with rfl|⟨j,rfl⟩
  · exact (ne rfl).elim
  · change _ ≤ ‖o-(o+t • z j)‖; simpa using under j
  · change _ ≤ ‖o+t • z i-o‖; simpa using under i
  change _ ≤ ‖o+t • z i - (o+t • z j)‖; rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul, Real.norm_of_nonneg tp.le,mul_comm]; exact mul_le_mul_of_nonneg_left (sep i j (fun h=>ne (Subtype.ext (congrArg far h)))) tp.le

variable {G:Gauge}{L:Register G}
def load (p:Node I J→L.Token):ℕ:= ∑i, (p (leaf i)).1
def carry (p:Node I J→L.Token):ℕ := ∑i,(p (far i)).1
def mass (p:Node I J→L.Token)(r t:ℝ):ℝ:=r^(load p)*t^(carry p)
theorem innerdeg (p:Node I J→L.Token):sigma (crop p (near I J))=load p:=by
  rw [sigma_set]; simp [near,load]
theorem outerdeg (p:Node I J→L.Token)(a:L.Token):sigma (crop (update p child a) (outer I J))=a.1+carry p:=by
  rw [sigma_set]; simp [outer,terminalS,carry]
theorem fee (p:Node I J→L.Token)(r t:ℝ)(n:ℕ):
    (frame I J).fee p (radius r t) (frame I J).leaves (frame I J).root n=mass p r t/t^n:=by
  rw [Arboreal.fee,Arboreal.rent,Tree.leaves,Finset.prod_union away]
  simp [mass,load,near,frame,radius,carry,terminalS,Finset.prod_pow_eq_pow_sum]
theorem prestige (r t:ℝ): Arboreal.prestige (frame I J) (radius r t)=(1+run t)*(1+run r):=by
  simp [Arboreal.prestige,frame,radius]
theorem ratio (r t:ℝ):(frame I J).ratioAt (radius r t) child=r/t:=rfl
end YM.OPE.Logged.Tree
