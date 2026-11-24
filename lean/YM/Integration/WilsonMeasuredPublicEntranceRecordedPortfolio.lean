import YM.Integration.WilsonMeasuredPublicEntranceRecordedPort

/-! The positive reflected detector uses only the previously named original raw
coordinates of its own Wick length, at the two original test positions. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4500
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRecordedPortfolio
open Function Extra.FD Maxwell Maxwell.Wick Labels MvPolynomial Table
open WilsonMeasuredPublicEntranceRecordedWick
open scoped Classical BigOperators
variable {G:Gauge}{F:Frames G}{d:ℕ}

theorem ranked (B:RStage F d)(q:ℕ)(z:(freeTable F).Field d)(correct:Length (writes F d z) q):
    z=∑j,if q=(B.w j).2 then B.b.repr z j • B.b j else 0:=by
  let layer:=weightedHomogeneousComponent (R:=ℂ) (letterCount (G:=G)) q
  have keep:layer (writes F d z)=writes F d z:=by
    simpa only [if_true] using weightedHomogeneousComponent_of_mem (m:=q)
      (show writes F d z∈weightedHomogeneousSubmodule ℂ letterCount q from correct)
  have each (j):layer (writes F d (B.b j))=if q=(B.w j).2 then writes F d (B.b j) else 0:=
    weightedHomogeneousComponent_of_mem (show writes F d (B.b j)∈weightedHomogeneousSubmodule ℂ letterCount (B.w j).2 from B.length j)
  apply writes_inj F d
  rw [←keep]
  conv_lhs => rw [←B.b.sum_repr z]
  rw [map_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases rank:q=(B.w j).2 <;> simp only [map_smul,each,rank,if_true,if_false,smul_zero,map_zero]

def cell (x y:E4)(z:(freeTable F).Field d)(a:(F.level d).Index):ℂ:=
  (freeTable F).classMoment (freeTable F) (fun _:Fin 2=>d) (couple x y) ![z,(freeTable F).project d (Pi.single a 1)]

theorem printed (x y:E4)(z:(freeTable F).Field d)(a:(F.level d).Index):
    readsTwo F d x y z ((freeTable F).project d (Pi.single a 1))=cell x y z a:=by
  let T:=freeTable F
  let peer:T.Field d:=T.project d (Pi.single a 1)
  let tags:Fin 2→T.Tag:=fun i=>⟨d,(![z,peer]:Fin 2→T.Field d) i⟩
  have appointed:(![⟨d,z⟩,⟨d,peer⟩]:Fin 2→T.Tag)=tags:=by
    funext i
    fin_cases i <;> rfl
  calc
    _=T.useAt T (couple x y) ![⟨d,z⟩,⟨d,peer⟩]:=scan_used F d x y z peer
    _=T.useAt T (couple x y) tags:=congrArg (T.useAt T (couple x y)) appointed
    _=cell x y z a:=rfl

theorem priced (B:RStage F d)(x y:E4)(i:Fin (B.m+1))(z:(freeTable F).Field d)
    (ε:ℝ)(ep:0≤ε)(actual:∀a:(F.level d).Index,((F.level d).grades a).2=(B.w i).2→‖cell x y z a‖≤ε):
    ‖read x y (B.b i) z‖≤(∑j,‖B.b.repr (faceTest F d x y (B.b i)) j‖)*ε:=by
  let v:=faceTest F d x y (B.b i)
  have homogeneous:Length (writes F d v) (B.w i).2:=by
    rw [show v=ride F (face (x-y)) d ((freeTable F).conj (table_spin F) d (B.b i)) from rfl,ride_at,writes_bar]
    exact turned _ _ (barred _ (B.length i))
  have expand:=ranked B (B.w i).2 v homogeneous
  change ‖readsTwo F d x y z v‖≤_
  conv_lhs => rw [expand]
  rw [map_sum,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>?_)
  by_cases rank:(B.w i).2=(B.w j).2
  · obtain ⟨a,pure,same⟩:=WilsonMeasuredPublicEntranceRecordedPort.selected F d B j
    rw [if_pos rank,map_smul,smul_eq_mul,norm_mul,←same,printed]
    exact mul_le_mul_of_nonneg_left (actual a ((congrArg Prod.snd pure).trans rank.symm)) (norm_nonneg _)
  · rw [if_neg rank,map_zero,norm_zero]
    exact mul_nonneg (norm_nonneg _) ep
end YM.Integration.WilsonMeasuredPublicEntranceRecordedPortfolio
end
