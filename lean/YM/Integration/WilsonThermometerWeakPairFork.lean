import YM.Integration.WilsonThermometerWeakNestedChild

/-! The two actual near points and the independently positioned far field.
The root is 0, its near child is 1, and the three leaves are 2, 3 and 4. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairFork
open Function Finset Filter Set OPE OPE.Arboreal
open scoped Topology BigOperators Classical

def frame:Arboreal (Fin 5) where
  root:=0
  zones:={0,1}
  parent:=![0,0,1,1,0]
  depth:=![0,1,2,2,1]
  direct:=rfl
  inward i:=by fin_cases i <;> decide
  step i h:=by fin_cases i <;> first | (exfalso;exact h rfl) | decide

theorem middle:frame.middle frame.zones={1}:=by ext j;fin_cases j <;> simp [Arboreal.middle,frame]
theorem leave:frame.leaves={2,3,4}:=by ext j;fin_cases j <;> simp [Arboreal.leaves,Arboreal.live,frame]
theorem pruned:frame.live (frame.zones.erase 1)={1,4}:=by ext j;fin_cases j <;> simp [Arboreal.live,frame]

def position (r t:ℝ)(x y z:E4):Fin 5→E4:=![0,0,r • x,r • y,t • z]
def radius (r t:ℝ):Fin 5→ℝ:=![t,r,r,r,t]

private lemma tips {i j:Fin 5}(e:i∉frame.zones)(a:frame.Anc i j):i=j:=by
  by_contra ne
  exact e (a.proper (Ne.symm ne))

private lemma branch {j:Fin 5}(a:frame.Anc 1 j):j=1 ∨ j=2 ∨ j=3:=by
  fin_cases j
  · exact ((show (1:Fin 5)≠0 by decide) a.excess).elim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · have lt:=a.into (by decide)
    change (1:ℕ)<1 at lt
    omega

lemma inputs:frame.inputs frame.zones 1={2,3}:=by
  ext j
  change j∈frame.leaves.filter (frame.Anc 1) ↔ _
  rw [leave,mem_filter]
  constructor
  · rintro ⟨h,h'⟩
    rcases branch h' with rfl|rfl|rfl <;> simp_all
  · rintro h
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using h : j=2 ∨ j=3) with rfl|rfl
    · exact ⟨by decide,Arboreal.Anc.step frame 2⟩
    · exact ⟨by decide,Arboreal.Anc.step frame 3⟩

theorem actual {r t M δ:ℝ}{x y z:E4}(hr:0<r)(rt:r≤t)(m:0≤M)
    (hx:‖x‖≤M)(hy:‖y‖≤M)(hz:‖z‖≤M)(fz:2*δ≤‖z‖)
    (sep:δ≤‖x-y‖)(room:r*M≤t*δ) :
    frame.Convoy M δ (radius r t) (position r t x y z):=by
  have ht:0<t:=hr.trans_le rt
  have upx:‖r • x‖≤M*r:=by rw [norm_smul,Real.norm_of_nonneg hr.le,mul_comm];gcongr
  have upy:‖r • y‖≤M*r:=by rw [norm_smul,Real.norm_of_nonneg hr.le,mul_comm];gcongr
  have upz:‖t • z‖≤M*t:=by rw [norm_smul,Real.norm_of_nonneg ht.le,mul_comm];gcongr
  have far (j:Fin 5)(a:frame.Anc 1 j):
      δ*t≤‖position r t x y z j-position r t x y z 4‖:=by
    have bound:‖position r t x y z j‖≤t*δ:=by
      rcases branch a with rfl|rfl|rfl
      · change ‖(0:E4)‖≤t*δ;simpa using (mul_nonneg hr.le m).trans room
      · exact upx.trans ((mul_comm M r) ▸ room)
      · exact upy.trans ((mul_comm M r) ▸ room)
    have cut:2*(t*δ)≤‖position r t x y z 4‖:=by
      change _≤‖t • z‖
      rw [norm_smul,Real.norm_of_nonneg ht.le]
      linarith only [mul_le_mul_of_nonneg_left fz ht.le]
    linarith only [norm_sub_norm_le (position r t x y z 4) (position r t x y z j),
      norm_sub_rev (position r t x y z 4) (position r t x y z j), bound,cut,mul_comm t δ]
  have kid0:frame.kids 0={1,4}:=by ext j;fin_cases j <;> simp [Arboreal.kids,frame]
  have kid1:frame.kids 1={2,3}:=by ext j;fin_cases j <;> simp [Arboreal.kids,frame]
  have close:δ*r≤‖r • x-r • y‖:=by
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
    exact mul_le_mul_of_nonneg_left sep hr.le
  constructor
  · constructor
    · intro i hi; rcases (by simpa [frame] using hi : i=0 ∨ i=1) with rfl|rfl
      exacts [ht,hr]
    · intro i hi; rcases (by simpa [frame] using hi : i=0 ∨ i=1) with rfl|rfl
      exacts [le_rfl,rt]
  · intro i
    fin_cases i
    · change ‖(0:E4)-0‖≤M*t;simpa using mul_nonneg m ht.le
    · change ‖(0:E4)-0‖≤M*t;simpa using mul_nonneg m ht.le
    · change ‖r • x-0‖≤M*r;simpa using upx
    · change ‖r • y-0‖≤M*r;simpa using upy
    · change ‖t • z-0‖≤M*t;simpa using upz
  · intro i j k hf
    have zone:=hf.inner
    obtain ⟨a,ha,b,hb,ne,hj,hk⟩:=hf
    rcases (by simpa [frame] using zone : i=0 ∨ i=1) with rfl|rfl
    · rw [kid0] at ha hb
      rcases (by simpa using ha : a=1∨a=4) with rfl|rfl <;>
        rcases (by simpa using hb : b=1∨b=4) with rfl|rfl
      · exact (ne rfl).elim
      · rw [←tips (by decide : (4:Fin 5)∉frame.zones) hk]
        exact far j hj
      · rw [←tips (by decide : (4:Fin 5)∉frame.zones) hj,norm_sub_rev]
        exact far k hk
      · exact (ne rfl).elim
    · rw [kid1] at ha hb
      rcases (by simpa using ha : a=2∨a=3) with rfl|rfl <;>
        rcases (by simpa using hb : b=2∨b=3) with rfl|rfl
      · exact (ne rfl).elim
      · rw [←tips (by decide : (2:Fin 5)∉frame.zones) hj,←tips (by decide : (3:Fin 5)∉frame.zones) hk]
        exact close
      · rw [←tips (by decide : (3:Fin 5)∉frame.zones) hj,←tips (by decide : (2:Fin 5)∉frame.zones) hk,norm_sub_rev]
        exact close
      · exact (ne rfl).elim

end YM.Integration.WilsonThermometerWeakPairFork
end
