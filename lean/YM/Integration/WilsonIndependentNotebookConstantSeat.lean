import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! Physical cutoff coordinates as constant thermal letters on their own test slot. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookConstantSeat
open Function Finset Lattice RG Wilson Source Labels XSpace XSpace.Rose XSpace.Cirrus
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain PowerSeries
open WilsonIndependentMatchedFiledIncome (plate allot charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Classical
variable {G:Gauge}{h D k:ℕ}{F:Labels.Frame G h}

def seat (F:Labels.Frame G h)(i:F.Index):Alma F:=
  ⟨(i,⟨0,by simp⟩),by simpa [rankS] using F.bound i⟩

def part (im:Bool)(z:ℂ):ℝ:=if im then z.im else z.re
def issue (F:Labels.Frame G h)(im:Bool)(w:F.Coeff):Verse F:=fun a=>
  if a=seat F (sheet F a) then C (part im (w (sheet F a))) else 0

@[simp] theorem seated (im:Bool)(w:F.Coeff)(i:F.Index):issue F im w (seat F i)=C (part im (w i)):=by
  simp [issue,sheet,seat]

private theorem seated_sum {U:Type*}[AddCommMonoid U](f:Alma F→U)
    (vacant:∀a,a≠seat F (sheet F a) → f a=0):
    ∑a,f a=∑i,f (seat F i):=by
  classical
  let seats:=Finset.univ.image (seat F)
  calc
    _=∑a∈seats,f a:=by
      symm
      apply Finset.sum_subset (subset_univ _)
      intro a _ missing
      apply vacant a
      exact fun eq=>missing (Finset.mem_image.mpr ⟨sheet F a,mem_univ _,eq.symm⟩)
    _=_:=Finset.sum_image (fun i _ j _ eq=>congrArg (sheet F) eq)

theorem constant (e:ℕ)(s A:ℝ):allot e (C s) A=(e+1:ℕ)* (|s| *A):=by
  have one (j:ℕ):(∑t∈Finset.HasAntidiagonal.antidiagonal j,|coeff t.1 (C s)| *A)=|s| *A:=by
    rw [Finset.sum_eq_single (0,j)]
    · simp
    · intro t ht ne
      have add:=Finset.HasAntidiagonal.mem_antidiagonal.mp ht
      have non:t.1≠0:=by
        intro eq
        apply ne
        exact Prod.ext eq (by simpa [eq] using add)
      rw [coeff_C_of_ne_zero non]
      simp
    · simp
  simp [allot,one,nsmul_eq_mul]

theorem exact_charge (e:ℕ)(im:Bool)(w:F.Coeff)(A:Alma F→ℝ):
    charge e (issue F im w) A=(e+1:ℕ)*∑i,|part im (w i)| *A (seat F i):=by
  unfold charge
  rw [seated_sum (fun a=>allot e (issue F im w a) (A a)) (by
    intro a ne
    simp [issue,ne,allot])]
  simp only [seated,constant,Finset.mul_sum]

theorem charged (e:ℕ)(im:Bool)(w:F.Coeff)(A:Alma F→ℝ)(M:ℝ)(hm:0≤M)
    (paid:∀i,A (seat F i)≤M):
    charge e (issue F im w) A≤(e+1:ℕ)*M*F.coeffSize w:=by
  rw [exact_charge,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro i _
  have fit:|part im (w i)| ≤ ‖w i‖:=by
    cases im with
    | false => exact Complex.abs_re_le_norm _
    | true => exact Complex.abs_im_le_norm _
  exact ((mul_le_mul_of_nonneg_left (paid i) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_right fit hm)).trans_eq (mul_comm ..)

private theorem stem_const (P:TowerS G D)(s:ℝ): Stem (C s) P=s • P:=by
  apply Prod.ext
  · exact funext fun n=>purePayment (P.1 n) s
  · exact purePayment P.2 s

theorem shrine (T:SectionData F)(fit:h<D)(im:Bool)(w:F.Coeff):
    Shrine (plate T fit) (issue F im w)=∑i,part im (w i) • vein (plate T fit) (seat F i):=by
  unfold Shrine
  rw [seated_sum (fun a=>Stem (issue F im w a) (vein (plate T fit) a)) (by
    intro a ne
    rw [show issue F im w a=C 0 by simp [issue,ne],stem_const,zero_smul])]
  simp only [seated,stem_const]

theorem scale (T:SectionData F)(fit:h<D)(im:Bool)(w:F.Coeff)(δ:ℝ):
    Shrine (plate T fit) (issue F im ((δ^h) • w))=
      (δ^h) • Shrine (plate T fit) (issue F im w):=by
  rw [shrine,shrine,Finset.smul_sum]
  apply sum_congr rfl
  intro i _
  have cut:part im (((δ^h) • w) i)=δ^h*part im (w i):=by
    cases im with
    | false => exact Complex.smul_re ..
    | true => exact Complex.smul_im ..
  rw [cut,mul_smul]

/-- The two surveys retain their own original finite wages before the cutoff
vector, real/imaginary component and all angular or thermal ranks are selected. -/
theorem named (R:Run G)(W:Initialize G)(survey:Bool)(fit:h<D)(cap:h≤k)(e u:ℕ):
    let F:=R.family.labels.level h
    let T:=sectionAt R W survey h
    ∃(A:Alma F→ℝ)(M:ℝ),0≤M ∧ ∀(im:Bool)(w:F.Coeff),
      let c:=issue F im w
      On k (Shrine (plate T fit) c) ∧ charge e c A≤(e+1:ℕ)*M*F.coeffSize w ∧ 
      ∀j r,j≤e→Fruit 0 1 u ((Shrine (plate T fit) c).2 j r) ((e+1:ℕ)*M*F.coeffSize w):=by
  intro F T
  obtain ⟨A,non,pay⟩:=WilsonIndependentMatchedFiledIncome.named R W survey h fit cap e u
  let M:=∑i:F.Index,A (seat F i)
  have hm:0≤M:=sum_nonneg fun i _=>non _
  have hi i:A (seat F i)≤M:=single_le_sum (f:=fun i=>A (seat F i)) (fun _ _=>non _) (mem_univ i)
  refine ⟨A,M,hm,?_⟩
  intro im w c
  have bill:=charged e im w A M hm hi
  exact ⟨(pay c).1,bill,fun j r bound=>((pay c).2.2 j r bound).more bill⟩

end YM.Integration.WilsonIndependentNotebookConstantSeat
