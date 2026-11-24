import YM.Integration.WilsonThermometerWeakPairFork

/-! The same near and far parents are used in the two single-scale estimates
and the joined child estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairRooms
open Filter Finset Set OPE OPE.Arboreal WilsonThermometerWeakPairFork
open scoped Topology BigOperators Classical

def near : Finset (Fin 5):={2,3}
def outside : Finset (Fin 5):={1,4}

theorem inner {r t M δ:ℝ}{x y z:E4}(hr:0<r)(hx:‖x‖≤M)(hy:‖y‖≤M)
    (sep:δ≤‖x-y‖):WithinRoom r M δ (crop (WilsonThermometerWeakPairFork.position r t x y z) near) 0:=by
  constructor
  · rintro ⟨i,hi⟩
    rcases (by simpa [near] using hi : i=2∨i=3) with rfl|rfl
    · change ‖r • x-0‖≤M*r
      rw [sub_zero,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
      gcongr
    · change ‖r • y-0‖≤M*r
      rw [sub_zero,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
      gcongr
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ ne
    have bound:δ*r≤‖r • x-r • y‖:=by
      rw [←smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm];gcongr
    rcases (by simpa [near] using hi : i=2∨i=3) with rfl|rfl <;>
      rcases (by simpa [near] using hj : j=2∨j=3) with rfl|rfl
    · exact (ne rfl).elim
    · exact bound
    · change _≤‖r • y-r • x‖
      rw [norm_sub_rev];exact bound
    · exact (ne rfl).elim

theorem outer {r t M δ:ℝ}{x y z:E4}(ht:0<t)(hm:0≤M)(hz:‖z‖≤M)
    (sep:δ≤‖z‖):WithinRoom t M δ (crop (WilsonThermometerWeakPairFork.position r t x y z) outside) 0:=by
  constructor
  · rintro ⟨i,hi⟩
    rcases (by simpa [outside] using hi : i=1∨i=4) with rfl|rfl
    · change ‖(0:E4)-0‖≤M*t
      simpa using mul_nonneg hm ht.le
    · change ‖t • z-0‖≤M*t
      rw [sub_zero,norm_smul,Real.norm_of_nonneg ht.le,mul_comm];gcongr
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ ne
    have bound:δ*t≤‖t • z‖:=by
      rw [norm_smul,Real.norm_of_nonneg ht.le,mul_comm];gcongr
    rcases (by simpa [outside] using hi : i=1∨i=4) with rfl|rfl <;>
      rcases (by simpa [outside] using hj : j=1∨j=4) with rfl|rfl
    · exact (ne rfl).elim
    · change _≤‖0-t • z‖;simpa using bound
    · change _≤‖t • z-0‖;simpa using bound
    · exact (ne rfl).elim

variable {G:Gauge}{L:Register G}
def load (p:Fin 5→L.Token):= (p 2).1+(p 3).1
def mass (p:Fin 5→L.Token)(r t:ℝ):=r^(load p)*t^(p 4).1

theorem innerdeg (p:Fin 5→L.Token) : sigma (crop p near)=load p:=by
  rw [sigma_set];simp [near,load]

theorem outerdeg (p:Fin 5→L.Token)(a:L.Token) :
    sigma (crop (Function.update p 1 a) outside)=a.1+(p 4).1:=by
  rw [sigma_set];simp [outside]

theorem fee (p:Fin 5→L.Token)(r t:ℝ)(n:ℕ):
    frame.fee p (radius r t) frame.leaves frame.root n=mass p r t/t^n:=by
  rw [Arboreal.fee,Arboreal.rent,leave]
  simp [mass,load,radius,frame,pow_add,mul_assoc]

theorem prestige (r t:ℝ):
    Arboreal.prestige frame (radius r t)=(1+run t)*(1+run r):=by
  simp [Arboreal.prestige,frame,radius]

theorem ratio (r t:ℝ):frame.ratioAt (radius r t) 1=r/t:=rfl

end YM.Integration.WilsonThermometerWeakPairRooms
end
