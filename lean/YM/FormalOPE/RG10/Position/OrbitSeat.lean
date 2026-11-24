import YM.FormalOPE.RG10.Position.Loft
import YM.FormalOPE.RG10.CommonStamps

/-!
# Link the reg-mixing rules (`LatticePT` moments) to our Gaussian library.
Finite regulated mark prescription prior to coupling/field conversions. On-shell lifts,
chosen once, may involve linear combinations of equal-weight pure stencil axes, prior to top
Wick mix. Use only particular normalization selected for WilsonX (post-H, retaining all orders;
no FPS over UV limits here). Doesn't use phase matrices or any cutoff-family OPE quotes.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  InversionTop Orb LatticePT Lattice Mixed Source Gauge Precision FlatFeed PowerSeries
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {F : Frames G} {h k r : ℕ} {n : Side} (hn : Even n.val)
    {I : Type*} [Fintype I] (w : I → LatticePT.Word G)
local notation "F₀" => feed (G:=G) hn
local notation "E" => vertices G n
private abbrev constChart (c:ℝ) : Observable G n := fun _=>c

-- on this particular regulator
private lemma raw_num (c:ℝ) : raw (constChart (G:=G) (n:=n) c)=outside (PowerSeries.C (c:ℂ)):=by
  unfold raw; funext x; apply PowerSeries.ext; intro i; change row i (InversionTop.lift _) x = coeff i _
  rw [row_lift]; change (↑(PertExtension.Series.Radial.jet (fun _:Dir G n => c) i x.2):ℂ) = _ -- namespace
  cases i
  · simp [outside]
  · simp [outside,PertExtension.Series.Radial.jet,iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]

private lemma delay_const {X:Type*}(c : RG10.Series) (f:Kernel X) : delay r (outside c*f)=outside c * delay r f:= by
  convert! delay_mul (outside c) f 0 r using 1 <;> simp

lemma paidOut (z : I→Site n) (ε:ℝ) (t:Task w) :
  let f:= fun i=> Stamp.native (z i) (w i).sound (w i).chosen (t i)
  let c := ∏ i, (w i).cost (t i) ε
  let A:=outside (C (c:ℂ)) * ∏ i, (f i).couplingMark
  lower (Mixed.number w t) (into (mk (Orb.diag (Orb.restrictedO (Mixed.product w univ t z ε))))) = (F₀).step E A := by
  intro f c A; let O:=Stamp.shafts f univ; let Q:=Orb.restrictedO (Mixed.product w univ t z ε)
  have ht:=Mixed.product_good w t z ε
  have hu:=Stamp.pre_all f univ
  have hr: Q = constChart c * Orb.restrictedO O:= by
    have he : Mixed.product w univ t z ε=(fun _=>c) * O:= by
      funext x; unfold Mixed.product; rw [prod_mul_distrib]; simp only [Pi.mul_apply]; unfold O Stamp.shafts; rw [Finset.prod_apply]; rfl
    unfold Q; rw [he]; rfl
  have ha : Uses.AtCoupling (Mixed.product w univ t z ε) (Mixed.number w t) A:=by
    unfold Uses.AtCoupling; change _ = raw Q
    rw [hr,raw_mul ?_ hu.curved]; swap; · exact ⟨continuous_const,contDiffAt_const⟩
    rw [raw_num]; unfold A; rw [delay_const]; exact congr_arg _ (Stamp.uses_all f univ)
  rw [Uses.advance hn ht.1 ha, lower_delay]

/-- Full top marked `Word` realization (not replacing circuit with just connected terms).
Vertices of bare stencils use UNIT negative slots cancellation before any position or frame. -/
def rental (w:LatticePT.Word G)(z:Site n) (ε:ℝ) := ∑ i:w.F.Index, outside (C ((w.cost i ε):ℂ)) *
     (Stamp.native z w.sound w.chosen i).couplingMark

private lemma crown (t : (i:I)→(w i).F.Index)(ε:ℝ): (∏ i,(C (((w i).cost (t i) ε):ℂ)))= PowerSeries.C (↑(∏ i, (w i).cost (t i) ε):ℂ) := by
  push_cast; rw [_root_.map_prod]

theorem leased (z : I→Site n) (ε:ℝ) :
    (F₀).Funded ((E).weight * ∏ i,rental (w i) (z i) ε) ∧ (F₀).step E (∏ i,rental (w i) (z i) ε)=
    ∑ t:Task w, lower (Mixed.number w t) (into (mk (Orb.diag (Orb.restrictedO (Mixed.product w univ t z ε))))) := by
  let f (i:I) (j:(w i).F.Index):= Stamp.native (z i) (w i).sound (w i).chosen j
  let y (i:I) (j:(w i).F.Index) := PowerSeries.C (((w i).cost j ε):ℂ)
  obtain ⟨h,e⟩:= combination y (fun i j=>(f i j).couplingMark) (fun t=>Stamp.integrals hn (fun i=>f i (t i)) univ)
  refine ⟨h, e.trans ?_⟩; apply sum_congr rfl; intro i _; unfold y; rw [paidOut hn w z ε i,step_external, crown ]
  · rfl
  exact Stamp.integrals hn (fun j=>f j (i j)) univ

section assembly
variable (H : Hol G) (S : ∀ d, SectionData (F.level d)) (hS : ∀ d, (S d).Sound H) (hP : ∀ d, Bid.pop (S d))
variable (U : Loft F) (u : I → Token F)
local notation "F'" i => F.level i

-- preserve both gradings, so phases/stresses choose lifts with this
abbrev length (x : Token F) := Deck.slots F x.1 ⟨⟨x.1,Nat.lt_succ_self _⟩,x.2⟩
abbrev owner (x : Token F) := deck F x.1 ⟨⟨x.1,Nat.lt_succ_self _⟩,x.2⟩
abbrev Library (x : Token F) := {j : (F' x.1).Index // (F' x.1).grades j=(x.1, length x)}
def enroll (x : Token F) (i : Library x) : LatticePT.Word G:= ⟨x.1,F' x.1, S _,H,hS _,hP _,i.val,congr_arg Prod.fst i.property⟩
def inkAt (x : Token F) (i : Library x) := (((F' x.1).coords (U.lift x.1 (owner x))) i.val).re
theorem tinted (hh : U.Level F) (x:Token F) :
    ∑ i:Library x,(↑(inkAt U x i):ℂ) • (F' x.1).basis i.val = U.lift x.1 (owner x) := by
  let y:=U.lift x.1 (owner x); let f:=F.level x.1; let c (j:f.Index) := (f.coords y j); let M:=(x.1,length x)
  let J : Finset f.Index:= univ.filter (fun i=> f.grades i=M)
  have hv : ∀ i, ↑((c i).re)=c i := by
    intro i; apply Complex.conj_eq_iff_re.mp
    change star (f.coords y i)=f.coords y i; rw [← f.conj_basis (v:=f.coords y), LinearEquiv.symm_apply_apply];
    have hx : realBar y=y := by unfold y owner; rw [hh.form,deck_real]
    rw [hx]
  have hp : y∈Grade M := hh.grade _ M (owner x) (grade_written ..)
  have he : ∑ i:f.Index,c i • f.basis i=y := f.basis.sum_repr y
  calc
    _ = ∑ i:Library x, c i.val • f.basis i.val := sum_congr rfl fun i _ => congr_arg (fun (v:ℂ)=>v • (F' x.1).basis i.val) (hv i.val)
    _ = ∑ i∈J, c i • f.basis i := by
      rw [sum_subtype (p:=fun i=>f.grades i=M) J (fun _=> by simp [J]) (fun i=> c i • f.basis i)]; -- maybe rfl
    _ = _:= Eq.trans (sum_subset (subset_univ _) (fun i _ hi=> by
      have ht : M ≠ f.grades i:=Ne.symm (by simpa [J] using hi); unfold c; rw [f.power_coefficient i ht hp, zero_smul])) he
lemma against (hh : U.Level F) (x:Token F) :
    ∑ i:Library x,(↑(inkAt U x i):ℂ) • electrical (enroll H S hS hP x i) = writes F x.1 (owner x) := by
  have he:= congr_arg (Maxwell.observable G x.1) (tinted U hh x); rw [_root_.map_sum,hh.warmth] at he; simp_rw [map_smul] at he; exact he



def membrane (x:Token F)(q : Site n)(ε:ℝ) := ∑ i:Library x, outside (C (inkAt U x i:ℂ)) * rental (enroll H S hS hP x i) q ε

theorem curtain (q:I→Site n) (ε:ℝ) : (F₀).Funded ((E).weight * ∏ i,membrane H S hS hP U (u i) (q i) ε) ∧
    (F₀).step E (∏ i,membrane H S hS hP U (u i) (q i) ε)=∑ Z:(∀ i, Library (u i)),
      (∏ i,C ((inkAt U (u i) (Z i)):ℂ)) * (F₀).step E (∏ i,rental (enroll H S hS hP (u i) (Z i)) (q i) ε) := combination
        (fun i j=>C (inkAt U (u i) j:ℂ)) (fun i j=>rental (enroll H S hS hP (u i) j) (q i) ε)
        (fun t=>(leased hn (fun i=>enroll H S hS hP (u i) (t i)) q ε).1)

local notation "o" => Deck.token F 0 (Deck.start F 0)

theorem membrane_unit (hh : U.Level F) (q:Site n)(ε:ℝ) : membrane H S hS hP U o q ε=outside (C (↑(ε^4):ℂ)) := by
  have ht:(F.level o.1).grades (0:(F.level o.1).Index)=(o.1,length o):=(F.level o.1).zero_degree |>.trans (grades_he) -- syntax
  let i:Library o:=⟨0,ht⟩
  have he := hh.unit o.1
  have hv : ∀ j:Library o,inkAt U o j=((Pi.single (M:=fun _=>ℂ) (0:(F.level o.1).Index) (1:ℂ)) j.val).re := fun j=> by
    unfold inkAt; rw [show owner o = (freeTable F).unit o.1 from ground F 0,he,(F.level o.1).coords_unit]; rfl
  unfold membrane
  rw [sum_eq_single_of_mem i (mem_univ _)];
  · rw [hv i]; dsimp only [i]
    rw [Pi.single_eq_same]; simp only [Complex.one_re,Complex.ofReal_one,map_one]
    rw [show outside 1= (1:Kernel (Unit × Dir G n)) from rfl,one_mul]
    let u:= enroll H S hS hP o i; change rental u q ε=_
    unfold rental
    have hk : ∀ j, u.cost j ε= ε^4 * Pi.single (M:=fun _=>ℝ) (0:u.F.Index) 1 j:= by intro j; unfold LatticePT.Word.cost; change ε^4/ε^0 * topBasis _ _ _ _ 0 _=_; rw [pow_zero,div_one]; exact congr_arg (fun x => ε^4*x) (congr_fun (topBasis_unit u.S u.H u.sound u.chosen) j)
    rw [sum_eq_single_of_mem (0:u.F.Index) (mem_univ _)]
    · rw [hk 0, Pi.single_eq_same,Stamp.nativeUnit,mul_one, mul_one]
    intro j _ hj; rw [hk j,Pi.single_eq_of_ne hj,mul_zero,Complex.ofReal_zero,map_zero,show outside 0=(0:Kernel (Unit × Dir G n)) from rfl,zero_mul]
  intro j _ hj; rw [hv j,Pi.single_eq_of_ne (show j.val≠0 from fun h=>hj (Subtype.ext h))]; simp only [Complex.zero_re,Complex.ofReal_zero,map_zero]; exact zero_mul _
where grades_he : ((0,0):ℕ ×ℕ)=(o.1,length o):=(grades_ground F 0).symm

/-- Real regulator prescription, including literal lattice origin averaging at common period
(putting tests in WilsonX measurement-length units). `ℝ⟦g_N⟧`. -/
def prelude (q:ℕ+)(m:ℕ)(ψ : (I→E4)→ℝ) := ∑ Z:(∀ i,Library (u i)),
    (PowerSeries.C (∏ i,inkAt U (u i) (Z i))) * mk (Mixed.polynomialTop (fun i=>enroll H S hS hP (u i) (Z i)) q m ψ)

lemma into_C (r : ℝ) : into (C r) = C (r:ℂ):= PowerSeries.map_C ..
lemma insideXY (q : ℕ+) (m : ℕ)(ψ : (I→E4)→ℝ):
    let g:= feed (G:=G) (side_even q m); let n:=LatticePT.side q m
    let Q := ∑ x:I→Native q m,∑ z∈origins q m, PowerSeries.C ((Mixed.price q m ψ x):ℂ) *
         g.step (vertices G n) (∏ i, rental (w i) (x i + z) (epsilon q m))
    into (mk (Mixed.polynomialTop w q m ψ)) = Q := by
  intro g n Q; unfold Q; ext p : 1
  simp only [into_coeff,coeff_mk,Mixed.polynomialTop,Complex.ofReal_mul,Complex.ofReal_sum, _root_.map_sum, coeff_C_mul]
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro z _; rw [← Finset.mul_sum]; unfold g n;
  congr 1
  rw [(leased (G:=G) (side_even q m) w (fun i=>x i+z) (epsilon q m)).2, _root_.map_sum]
  apply sum_congr rfl; intro i _; simp only [lower,coeff_mk,into_coeff]; rfl

theorem coordinate (q : ℕ+)(m:ℕ)(ψ : (I→E4)→ℝ):
    let g:= feed (G:=G) (side_even q m); let n:=LatticePT.side q m;
    into (prelude H S hS hP U u q m ψ) = ∑ x:I→Native q m,∑ z∈origins q m, PowerSeries.C ((Mixed.price q m ψ x) : ℂ) *
         g.step (vertices G n) (∏ i, membrane H S hS hP U (u i) (x i+z) (epsilon q m)) := by
  intro g n; unfold g n prelude; simp_rw [(curtain (side_even ..) H S hS hP U u (fun _=>_) _).2] -- maybe
  simp_rw [_root_.map_sum,_root_.map_mul,into_C, insideXY (G:=G), Finset.mul_sum,Complex.ofReal_prod,_root_.map_prod]
  rw [sum_comm]; apply sum_congr rfl; intro x _; rw [sum_comm]; apply sum_congr rfl; intro z _; apply sum_congr rfl; intro i _; ring
end assembly
end YM.FormalOPE.RG10.Position
