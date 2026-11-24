import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Geometry
/-! # Child and Parent at the same tree actual placements. Proof adaptation of
`Integration/WilsonPublicForkRooms`. Keep both radius powers incl Far occupancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Finset Function Set Table Arboreal Log Node
open scoped Topology BigOperators Classical
variable {I J:Type} [Fintype I] [Fintype J]
theorem names (u:↥(near I J)):∃i,u.1=leaf i:=by obtain ⟨i,_,e⟩:=Finset.mem_map.mp u.2; exact ⟨i,e.symm⟩
def nearSeat : I≃↥(near I J):=Equiv.ofBijective (fun i=>(⟨leaf i,near_mem i⟩:↥(near I J))) ⟨by
  intro i j eq;exact leaf.inj (congrArg Subtype.val eq),by
  intro u;obtain ⟨i,hi⟩:=names u;exact ⟨i,Subtype.ext hi.symm⟩⟩
theorem seats (u:Node I J) : u∈outer I J ↔ u=child ∨ ∃ j,u=far j:=by cases u <;>simp [outer,rim]
theorem inner (o:E4) {r t M δ:ℝ}{x:I→E4}{z:J→E4}(rp:0<r)
    (cl:∀i,‖x i‖≤M)(sep:∀i j,i≠j→δ≤‖x i-x j‖) : WithinRoom r M δ (crop (sites o r t x z) (near I J)) o := by
  obtain ⟨hp,hq⟩:=only_room o rp cl sep; constructor
  · intro u; obtain ⟨i,hi⟩:=names u; specialize hp i; unfold crop; rw [hi]; exact hp
  intro u v ne; obtain ⟨i,hi⟩:=names u; obtain ⟨j,hj⟩:=names v; unfold crop; rw [hi,hj]; exact hq i j (fun e=> ne (Subtype.ext (hi.trans ((congrArg leaf e).trans hj.symm))))

theorem outside (o:E4) {r t M δ:ℝ}{x:I→E4}{z:J→E4}
    (h : Ready r t M δ x z) (mn:0≤M)(dn:0≤δ) : WithinRoom t M δ (crop (sites o r t x z) (outer I J)) o := by
  obtain ⟨hp,hq⟩:= only_room o (h.length.trans_le h.adj) h.reaches h.separated; constructor
  · rintro ⟨i,hi⟩; rcases (seats i).mp hi with rfl|⟨j,rfl⟩
    · simpa [crop,sites] using mul_nonneg mn (h.length.trans_le h.adj).le
    exact hp j
  rintro ⟨i,hi⟩ ⟨j,hj⟩ ne; rcases (seats i).mp hi with rfl|⟨i,rfl⟩ <;> rcases (seats j).mp hj with rfl|⟨j,rfl⟩
  · exact (ne rfl).elim
  · exact middle_far o h dn _ (.same ..) j
  · rw [norm_sub_rev]; exact middle_far o h dn _ (.same ..) i
  exact hq i j (fun e=>ne (Subtype.ext (congrArg far e)))

variable {G:Gauge}{L:Register G}
def load (p:Node I J→L.Token):ℕ := ∑i,(p (leaf i)).1
def duty (p:Node I J→L.Token):ℕ := ∑j,(p (far j)).1
def mass (p:Node I J→L.Token)(r t:ℝ):ℝ := r^(load p)*t^(duty p)

theorem innerdeg (p:Node I J→L.Token):sigma (crop p (near I J))=load p:=by
  rw [sigma_set];simp [near,load]
theorem outerdeg (p:Node I J→L.Token)(a:L.Token):sigma (crop (update p child a) (outer I J))=a.1+duty p:=by
  rw [sigma_set]; simp [outer,rim,duty,Function.update]
lemma distinct : Disjoint (near I J) (rim I J) := Finset.disjoint_left.mpr fun i=>by cases i <;>simp [near,rim]
theorem fee (p:Node I J→L.Token)(r t:ℝ)(n:ℕ):
    (frame I J).fee p (radius r t) (frame I J).leaves (frame I J).root n=mass p r t/t^n:=by
  rw [Arboreal.fee,Arboreal.rent,leaves,Finset.prod_union distinct]
  simp [mass,load,duty,near,rim,frame,radius,Finset.prod_pow_eq_pow_sum]
omit [Fintype I] [Fintype J] in
theorem prestige (r t:ℝ): Arboreal.prestige (frame I J) (radius r t)=(1+run t)*(1+run r):=by
  simp [Arboreal.prestige,frame,radius]
omit [Fintype I] [Fintype J] in
theorem ratio (r t:ℝ):(frame I J).ratioAt (radius r t) child=r/t:=rfl
end YM.OPE.Flash259HorizonFork
