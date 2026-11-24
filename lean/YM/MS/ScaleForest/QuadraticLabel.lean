import YM.MS.ScaleForest.RoseTensor

/-!
# Fix **actual labels** for F12 and chiral curvature-pair applications

Specify two-arm family on-shell Maxwell Taylor site at `(4,2)`,
real weights, persistent through Film0 and both books. `basicPrice` holds
at *all couplings*. Neither the F12 nor the honest chiral pole
components enter as anonymous Laurent candidates.

In `planeMark` normalize as in the proposed examples 4f8 and 164: squared
F¹² with Taylor coefficient **1/2**, i.e. coefficient one after the
permutation of two slots. This is NOT as in 6e (factor four on the example
with two insertions). Color contraction using the actual color basis.
Here axis indices begin at 0 (thus (0,1) in `face12`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Quadratic
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo Theater
open FVA2.Position FVA2.Position.OpenAxis WilsonMS
open Lattice Momentum XSpace XSpace.Chiral XSpace.Normalize Maxwell Maxwell.Free Cylinder
open scoped Topology ContDiff InnerProductSpace

abbrev LSpec := XSpace.Chiral.P
structure Pupil where
  axes : LSpec → PlaqAxes → ℝ
  density : LSpec → ℝ
variable (X:Pupil)
variable {G : Gauge} {m d : ℕ}

def face12 : PlaqAxes:= ⟨⟨0,1⟩,by decide⟩
def planeMark: Pupil:= ⟨fun _ a=> if a=face12 then 1 else 0, fun j=>if j=0 then 1 else 0⟩
def chiralMark (σ:Bool): Pupil:= ⟨ fun i a=> q σ i (six a) (endr a),fun _=> Rose.f^2⟩

variable (G)
def armSite (i:LSpec): Flavor 0 := ∑ j:PlaqAxes,X.axes i j • Maxwell.Free.cell (six j) (endr j)
def onField : Maxwell.WickPol G := (2:ℂ)⁻¹ • ∑ i:LSpec, (X.density i:ℂ) • ( Maxwell.Free.team G (armSite X i) (armSite X i))
theorem onField_plane : onField planeMark G = (2:ℂ)⁻¹ • Maxwell.Free.team G (Maxwell.Free.cell 0 1) (Maxwell.Free.cell 0 1) := by
   unfold onField; have hu (i:P): armSite planeMark i = Maxwell.Free.cell 0 1:= by simp [armSite,planeMark,ite_smul,face12,six,endr]
   simp_rw [hu]; simp [planeMark,apply_ite,ite_smul]
theorem onField_Rose : onField (chiralMark false) G=(Rose.tin G).val := by
   unfold onField; change (2:ℂ)⁻¹ • (∑ i:LSpec,(↑(Rose.f^2:ℝ):ℂ) • Maxwell.Free.team G (Fq false i) (Fq false i))=(↑Rose.f:ℂ)^2 • U G
   push_cast; rw [ understand, ← Finset.smul_sum,smul_comm]

def focused : XSpace.Normalize.Sec G 6:= ⟨ onField X G, by
   apply Submodule.smul_mem; apply Submodule.sum_mem; intro i _; exact Submodule.smul_mem _ _ (team_label _ _ (by decide))⟩
theorem focus_tin : focused (chiralMark false) G= Rose.tin G:= Subtype.ext (onField_Rose G)

theorem focus_grade : MvPolynomial.IsWeightedHomogeneous bwt (onField X G) (4,2) := by
    unfold onField; apply (MvPolynomial.weightedHomogeneousSubmodule ℂ bwt (4,2)).smul_mem; apply MvPolynomial.IsWeightedHomogeneous.sum; intro i _;
    apply (MvPolynomial.weightedHomogeneousSubmodule ℂ bwt (4,2)).smul_mem; apply MvPolynomial.IsWeightedHomogeneous.sum; intro j _;
    let p:= (Maxwell.Free.flavor (G:=G) 0 j (armSite X i)); have h:=symbol_hom p (fun i=>(i+2,(1:ℕ)))
    exact h.mul h

theorem focus_real : reel 6 (focused X G)=focused X G:= by
   apply Subtype.ext; change realForm (onField X G)=onField X G; unfold onField; simp only [map_sum,real_scale,realTeam,star_inv₀,star_ofNat, show ∀ x:ℝ, star (x:ℂ)=_ from fun x=>Complex.conj_ofReal x]

def registered : Theater.Film0 G 4 2 := ⟨On.lifting (focused X G).val,(Theater.cinema _).mpr
   ⟨ (Labels.pure_grade ..).mp (On.section_grade (focused X G) (focus_grade X G)), (On.fits (focused X G)).2,
      by rw [← On.lift_conj]; exact congr_arg On.lifting (congr_arg Subtype.val (focus_real X G))⟩ ⟩

theorem tin_woven : registered (chiralMark false) G = roseLift G := Subtype.ext (congr_arg On.lifting (onField_Rose G))

def enrol (n:ℕ) := withSource (invoice _ _ _ (registered X G)) (invoiceC (registered X G)) n

theorem tin_enrol (n:ℕ): enrol (chiralMark false) G n = roseMark G n:= by unfold enrol roseMark; simp_rw +unfoldPartialApp [tin_woven]
variable {G}

/-- For `planeMark` use the unit antisymmetric pair component. For
Rose use `q` tensors of `Trinity` and already keep the factor `Rose.f^2`
in `density`. -/
def firstCurl (g:ℂ)(i:Name G): Arts.Rack G m:= ∑ j:PlaqAxes, (X.axes i.1 j:ℂ) • cur g (chair m (six j)) (chair m (endr j)) i.2

def quadraticArm (g:ℂ): Arts.Rack G m:= (2:ℂ)⁻¹ • ∑ i:Name G, (X.density i.1:ℂ) • bite _ _ (firstCurl X g i) (firstCurl X g i)
theorem first_lift (p:Name G)(g:ℂ) : seed G (On.lifting (bit (armSite X p.1) p.2)) g m= firstCurl X g p:= by
   unfold bit; rw [show (symbol 0 (flavor (G:=G) 0 p.2 (armSite X p.1)))=∑ a:PlaqAxes, (X.axes p.1 a:ℂ) • symbol 0 (flavor (G:=G) 0 p.2 (Maxwell.Free.cell (six a) (endr a))) from ?_]; simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,ramp_curl, firstCurl]
   apply equalPol; intro A; unfold armSite; rw [symbol_test]; simp only [map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply,symbol_test, Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul]

set_option maxHeartbeats 1000000 in
theorem basicPrice (G: Gauge)(m:ℕ)(g:ℂ): value (Mob G) g (invoice _ _ _ (registered X G)) m = quadraticArm X g := by
    rw [OpenAxis.priceR]; change seed G (On.lifting (onField X G)) g m=_
    unfold onField quadraticArm Maxwell.Free.team; simp only [map_mul,map_sum,map_smul,Fintype.sum_prod_type, Finset.sum_apply,Pi.smul_apply,seed_p, Finset.smul_sum,
      show ∀ (i:LSpec)(c:G.ColorIndex), seed G (On.lifting (bit (armSite X i) c)) g m =firstCurl X g (i,c) from fun i c=> first_lift X (i,c) g]

lemma term0 (G:Gauge)(m:ℕ) : (enrol X G 0).symbol m = quadraticArm X 0 := by rw [ show (enrol X G 0).symbol=_ from Mach.onZero (invoice _ _ _ (registered X G)), basicPrice ]
lemma term_grade (G:Gauge) : (enrol X G 0).rank=2:= rfl

def rampLeg (j:PlaqAxes)(i : Name G)(s:L m) (p:SectorP m)(c:G.ColorIndex) : ℂ:= if c=i.2 then
    Complex.I * (polar0 (chair m (six j)) (chair m (endr j)) s p:ℂ) else 0

def antenna (i:Name G) (s:L m)(c:G.ColorIndex)(p:SectorP m) := ∑ j:PlaqAxes, (X.axes i.1 j:ℂ) * rampLeg j i s p c

lemma CurlPrice (i:Name G) (s:L m)(c:G.ColorIndex)(p:SectorP m): firstCurl X 0 i [vec s c p]= antenna X i s c p:= by unfold firstCurl antenna; simp only [cur,zero_smul,add_zero, Finset.sum_apply,vec,f_ref, Pi.smul_apply]; rfl

theorem Uses_first (i:Name G) : rank 1 (firstCurl (m:=m) X 0 i) ∧ Uses (setOf isA) (firstCurl (m:=m) X 0 i):= by
    have ht : rank 1 (firstCurl (m:=m) X 0 i):= by unfold firstCurl cur; simp only [zero_smul,add_zero]; exact Rails.sum _ fun j _=> (rank_α _ _ _).smul _
    refine ⟨ht,fun l j hj hh=>?_⟩; by_cases hp:l.length=1
    · obtain ⟨p,rfl⟩:= List.length_eq_one_iff.mp hp; rw [List.mem_singleton] at hj; subst p; obtain ⟨j,p⟩:=j
      unfold firstCurl cur; simp only [zero_smul,add_zero,Finset.sum_apply, Pi.smul_apply,c_α, show ∀ i k, j ≠ at_g i k from fun i k h=> hh ⟨_,_,h⟩,if_false,mul_zero,sub_self,smul_zero,Finset.sum_const_zero]
    exact ht _ (by rw [mod_int]; omega)

theorem Uses_quad : GaugeLegs (enrol X G 0).symbol:= by intro m; rw [term0]; exact Uses.smul _ (Uses.sum fun i _=> Uses.smul _ (Uses.pair (Uses_first X i).2 (Uses_first X i).2))

def weightedArm (i:Name G)(c:ℂ) :ℂ:= ↑(X.density i.1)*c

theorem takesA (m:ℕ)(i j:L m)(a b:G.ColorIndex)(p q:SectorP m): (enrol X G 0).symbol m [vec i a p,vec j b q]=∑ y:Name G, weightedArm X y ( antenna X y i a p * antenna X y j b q):= by
   simp only [term0,quadraticArm,Pi.smul_apply,Finset.sum_apply,bite,pairv (Uses_first X _).1 (Uses_first X _).1, CurlPrice,
       show field parity (vec i a p)=false from rfl,cross_false,one_mul,smul_eq_mul,Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _=> by unfold weightedArm; ring)

end YM.MS.ScaleForest.Quadratic
