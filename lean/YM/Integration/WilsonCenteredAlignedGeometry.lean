import YM.Integration.WilsonCenteredAlignedPhysicalRegularity
import YM.OPE.Eye.Cloud

/-! Each genuine child uses its own residue class on one reporting lattice.
All stencil coordinates move by the stated normalized mesh, including those
used between interpolation nodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredAlignedGeometry
open Function Filter Set Finset Metric WithLp Lattice OPE OPE.Stencils
open scoped Topology Classical BigOperators
abbrev Coord (n:ℕ):=Fin n × Axis

def linear (n:ℕ) : (Coord n→ℝ) →ₗ[ℝ] Points n where
  toFun y:=toLp 2 (fun i:Fin n=>toLp 2 (fun a:Axis=>y (i,a)))
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def assemble (n:ℕ) : (Coord n→ℝ) →L[ℝ] Points n where
  toLinearMap:=linear n
  cont:=by
    change Continuous (fun y:Coord n→ℝ=>toLp 2 (fun i:Fin n=>toLp 2 (fun a:Axis=>y (i,a))))
    exact (PiLp.continuous_toLp 2 (fun _:Fin n=>E4)).comp (continuous_pi (fun i=>
      (PiLp.continuous_toLp 2 (fun _:Axis=>ℝ)).comp (continuous_pi (fun a=>continuous_apply (i,a)))))

def chart {n:ℕ} (x:Points n):Coord n→ℝ:=fun v=>x v.1 v.2

def offset {n:ℕ} (W:Finset E4) (h:ℝ):Coord n→ℝ:=fun v=>h*Cloud.residue W h v.1 v.2

def step (n:ℕ) (W:Finset E4) (h:ℝ):ℝ:=h*Cloud.count (Fin n) W

def shot {n:ℕ} (W:Finset E4) (h:ℝ) (y:Coord n→ℝ):Points n:=
  assemble n (offset W h+y)

def unit {n:ℕ} (v:Coord n):Points n:=assemble n (Pi.single v 1)

theorem start {n:ℕ} (W:Finset E4) (h:ℝ) (x:Points n) :
    shot W h (chart x-offset W h)=x:=by
  have cancel:offset W h+(chart x-offset W h)=chart x:=by abel
  rw [shot,cancel]
  rfl

theorem positive (n:ℕ) (W:Finset E4) {h:ℝ} (hp:0<h):0<step n W h:=
  mul_pos hp (Int.cast_pos.mpr (Cloud.count_pos (I:=Fin n) W))

theorem unit_bound {n:ℕ} (v:Coord n): ‖unit v‖≤‖assemble n‖:=by
  have size:‖(Pi.single v (1:ℝ):Coord n→ℝ)‖≤1:=by
    rw [Pi.norm_single];norm_num
  exact ((assemble n).le_opNorm _).trans ((mul_le_mul_of_nonneg_left size (norm_nonneg _)).trans_eq (mul_one _))

private theorem place {n:ℕ} (y:Coord n→ℝ) (v:Coord n) (t:ℝ):
    update y v (y v+t)=y+t • (Pi.single v (1:ℝ)):=by
  ext w
  by_cases eq:w=v
  · subst w;simp
  · simp [Function.update_of_ne eq,Pi.single_eq_of_ne eq]

theorem line {n:ℕ} (W:Finset E4) (h:ℝ) (y:Coord n→ℝ) (v:Coord n) (t:ℝ):
    shot W h (update y v (y v+t)) = shot W h y+t • unit v:=by
  rw [place,shot,←add_assoc,map_add,map_smul];rfl

theorem tube {n:ℕ} (W:Finset E4) {h:ℝ} (hp:0<h) (L:ℕ) (x:Points n)
    (y:Coord n→ℝ) (v:Coord n) (half:Partway L (step n W h) [v] (chart x-offset W h) y)
    {t:ℝ} (time:t∈Icc 0 (step n W h*(L+3))) :
    dist (shot W h y+t•unit v) x ≤‖assemble n‖*(step n W h*(L+3)):=by
  let p:=chart x-offset W h
  let z:=update y v (y v+t)
  have hi:0 ≤ step n W h*(L+3):=mul_nonneg (positive n W hp).le (by positivity)
  have dims: ‖z-p‖ ≤ step n W h*(L+3):=(pi_norm_le_iff_of_nonneg hi).mpr (fun j=>by
    change |z j-p j|≤_
    by_cases eq:j=v
    · subst j
      rw [show z v=y v+t from update_self ..,(half v).1 List.mem_cons_self,add_sub_cancel_left,abs_of_nonneg time.1]
      exact time.2
    · have here: j∉[v]:=by simpa using eq
      have paid:0≤y j-p j ∧ y j-p j≤_ :=(half v).2 j here
      rw [show z j=y j from update_of_ne eq ..,abs_of_nonneg paid.1]
      exact paid.2)
  change dist (shot W h y+t•unit v) x≤_
  rw [←line,←start W h x,dist_eq_norm]
  change ‖assemble n (offset W h+z)-assemble n (offset W h+p)‖≤_
  rw [←map_sub,show offset W h+z-(offset W h+p)=z-p by abel]
  exact ((assemble n).le_opNorm _).trans (mul_le_mul_of_nonneg_left dims (norm_nonneg _))

theorem full_tube {n:ℕ} (W:Finset E4) {h:ℝ} (hp:0<h) (L:ℕ) (x:Points n)
    (y:Coord n→ℝ) (sample:valid L (step n W h) (univ:Finset (Coord n)).toList (chart x-offset W h) y):
    dist (shot W h y) x ≤ ‖assemble n‖*(step n W h*(L+3)):=by
  let p:=chart x-offset W h
  have hi:0 ≤ step n W h*(L+3):=mul_nonneg (positive n W hp).le (by positivity)
  have dims:‖y-p‖ ≤ step n W h*(L+3):=(pi_norm_le_iff_of_nonneg hi).mpr (fun j=>by
    obtain ⟨node,equal⟩:=(sample j).1 (by simp)
    change |y j-p j|≤_
    rw [equal]
    exact (abs_of_nonneg (step_near L _ (positive n W hp) node).1.le).le.trans (step_near L _ (positive n W hp) node).2)
  rw [←start W h x,dist_eq_norm]
  change ‖assemble n (offset W h+y)-assemble n (offset W h+p)‖≤_
  rw [←map_sub,show offset W h+y-(offset W h+p)=y-p by abel]
  exact ((assemble n).le_opNorm _).trans (mul_le_mul_of_nonneg_left dims (norm_nonneg _))

theorem grid {n:ℕ} (W:Finset E4) {h r:ℝ} (hp:0<h) (S:Schedule) (s:ℕ)
    (scale:r*h=S.a s) (L:ℕ) (p y:Coord n→ℝ)
    (sample:valid L (step n W h) (univ:Finset (Coord n)).toList p y) :
    ∃ u:Fin n → Cover, (∀i,r•(shot W h y) i=S.gridPoint s (u i)) ∧
      Screen (fun i=>(shot W h y) i) ∧
      (∀i a,(u i a)%Cloud.count (Fin n) W=Cloud.residue W h i a) :=by
  choose j atNode using fun v:Coord n=>(sample v).1 (by simp)
  let index (v:Coord n):ℤ:=⌈p v/step n W h⌉+1+(j v).val
  let u (i:Fin n) (a:Axis):ℤ:=index (i,a)*Cloud.count (Fin n) W+Cloud.residue W h i a
  have situated (i:Fin n) (a:Axis): (shot W h y) i a=h*u i a:=by
    change h*Cloud.residue W h i a+y (i,a)=_
    rw [atNode];unfold u index steps step
    push_cast;ring
  have distinct (i:Fin n) (a:Axis):u i a%Cloud.count (Fin n) W=Cloud.residue W h i a:=by
    unfold u
    rw [Int.add_comm,Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (Cloud.residue_nonneg ..) (Cloud.residue_small ..)]
  refine ⟨u,?_,?_,distinct⟩
  · intro i
    ext a
    change r*(shot W h y) i a=S.a s*(u i a)
    rw [situated,←mul_assoc,scale]
  · intro a i j eq
    change (shot W h y) i a=(shot W h y) j a at eq
    rw [situated,situated] at eq
    have e:u i a=u j a:=by exact_mod_cast (mul_left_cancel₀ hp.ne' eq)
    apply Cloud.residue_inj W h a
    change Cloud.residue W h i a=Cloud.residue W h j a
    rw [←distinct i a,←distinct j a,e]

end YM.Integration.WilsonCenteredAlignedGeometry
