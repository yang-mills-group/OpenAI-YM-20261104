import YM.XSpace.ProbePoles
import YM.XSpace.JointNull
import YM.Next.MAXWELL.Steps
/-!
# Pole multiplier for undifferentiated curvature endpoints

Regular after q³, nontrivial, same line parameter for both endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.ProbeLine
open Set Filter Function MeasureTheory Maxwell Maxwell.Free Analysis
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
local notation "I" => Complex.I
variable {G:Gauge}
variable {m u x y:E4}

structure Sky (m u y:E4):Prop where
  works:u≠0
  vanished:cubic m u y=0
variable (h:Sky m u y)
include h
local notation "D" => drifts m u y
local notation "d" => corner m u y
lemma flare (a b:Axis): Proves (fun r:ℝ=> (↑(rsq (D r)^3*grad a (grad b Green) (D r)):ℂ)) (8*↑normal*(d a*d b)):= by
  have hx : ∀ᶠ r:ℝ in atTop, rsq (D r)^3 * grad a (grad b Green) (D r) = (-2 * normal * basis a b)*rsq (D r)+ 8*normal*(D r a*D r b):= by
    filter_upwards [wandering m u y h.works] with r hr
    rw [second_Green hr]; have hs := norm_pos_iff.mpr (show D r≠0 from hr)
    unfold rsq; field_simp
  let p := (↑((-2 * normal * basis a b : ℝ)):ℂ)
  have he:= ((Proves.unit p).mul (square_match m u y)).add ((Proves.unit ((8:ℂ)* ↑normal)).mul ((corner_match m u y a).mul (corner_match m u y b)))
  rw [h.vanished,mul_zero,zero_add] at he
  apply he.alter; filter_upwards [hx] with r hr; simp only [Pi.add_apply,Pi.mul_apply,hr]; push_cast; unfold p; push_cast; rfl -- inspect

def spangle (m u y:E4) (a b i j:Axis):ℂ:=
  8*↑normal*((↑(kr b i)*corner m u y a*corner m u y j-↑(kr b j)*corner m u y a*corner m u y i)-(↑(kr a i)*corner m u y b*corner m u y j-↑(kr a j)*corner m u y b*corner m u y i))

lemma reflective (a b i j:Axis): Proves (fun r:ℝ=> (↑(rsq (D r)^3 * bareCurl a b i j (D r)):ℂ)) (spangle m u y a b i j):= by
  let M:=cubic m u y
  let HP (i j:Axis)(r:ℝ):=rsq (D r)^3 * grad i (grad j Green) (D r)
  let L (p q i j:Axis)(r:ℝ) := kr p q* HP i j r
  let F (p q i j:Axis):ℂ := (kr p q:ℂ)* (8*↑normal*(d i*d j))
  have he p q i j: Proves (fun r:ℝ=> (↑(L p q i j r):ℂ)) (F p q i j) := by
    simp_rw [L, Complex.ofReal_mul]; exact (Proves.unit _).mul (flare h i j)
  have ht := ((he b i a j).sub (he b j a i)).sub ((he a i b j).sub (he a j b i))
  rw [show F b i a j-F b j a i-(F a i b j-F a j b i)=spangle m u y a b i j by unfold F spangle; ring] at ht
  apply ht.alter; filter_upwards [wandering m u y h.works] with r hr
  simp only [Pi.sub_apply, ← Complex.ofReal_sub]; apply congr_arg Complex.ofReal
  have hh (i j:Axis) (x y:ℝ) : (if i=j then 1 else 0)*(x*y)=x*(if j=i then y else 0):= by
    by_cases h:i=j; · simp [h]
    simp [h,Ne.symm h]
  simp only [bareCurl,Pi.sub_apply,Bare.opp_grad hr,L,HP, kr_eq,hh,mul_sub]

abbrev stage (c:G.ColorIndex)(p q:Flavor 0)(m u y:E4)(r:ℝ):ℂ:= ((rsq (drifts m u y r)^3* fare c p q (drifts m u y r):ℝ):ℂ)
lemma assuring (c:G.ColorIndex)(p q:Flavor 0) : ∃ C:ℂ, Proves (stage c p q m u y) C:= by
  have hc a b i j: ∃ C:ℂ,Proves (stage c (cell a b) (cell i j) m u y) C:= by
    have hp:= reflective h a b i j
    refine ⟨_,hp.alter ((wandering m u y h.works).mono fun r hr=>?_)⟩
    change (↑(_*bareCurl _ _ _ _ _):ℂ)=↑(rsq _^3*fare c _ _ _)
    rw [show fare c (cell a b) (cell i j) (D r)=bareCurl a b i j (D r) from ?_]
    have he:= raw_mixed (fun _:Fin 0=>0) (fun _:Fin 0=>0) a b i j c c hr
    rw [if_pos rfl,pow_zero,one_mul, Tensor.coeff_apply_zero] at he; rw [Tensor.coeff_apply_zero] at he; exact he
  have hh (p:Flavor 0):p∈ Submodule.span ℝ {x|∃ a b: Axis, a<b∧ x=cell a b} := cell_span.symm ▸ Submodule.mem_top
  let W (p q:Flavor 0):Prop:= ∃ C:ℂ, Proves (stage c p q m u y) C
  have hy (z:Flavor 0): W z 0 ∧ W 0 z:= by
    have hp (x) (hx:x≠0): fare c z 0 x=0∧ fare c 0 z x=0:= ⟨map_zero (assay c hx 0 0 z),LinearMap.congr_fun (map_zero (assay c hx 0 0)) z⟩
    exact ⟨⟨0,(Proves.unit _).alter ((wandering m u y h.works).mono fun r hr=> by simp only [stage,(hp (D r) hr).1, mul_zero,Complex.ofReal_zero])⟩,
      ⟨0,(Proves.unit _).alter ((wandering m u y h.works).mono fun r hr=> by simp only [stage,(hp (D r) hr).2,mul_zero,Complex.ofReal_zero])⟩⟩
  have he (p p' q : Flavor 0) (hp: W p q) (hq: W p' q): W (p+p') q:= by
    obtain ⟨x,hx⟩:= hp; obtain ⟨y',hy⟩:=hq; refine ⟨_,(hx.add hy).alter ?_⟩
    filter_upwards [wandering m u y h.works] with r hr; simp only [Pi.add_apply,stage,show fare c (p+p') q _=_ from LinearMap.congr_fun ((assay c hr 0 0).map_add p p') q, LinearMap.add_apply,← fare_pair c p q (x:=D r) hr,← fare_pair c p' q (x:=D r) hr,mul_add,Complex.ofReal_add]
  have hu (p q q' : Flavor 0) (hp: W p q) (hq: W p q'): W p (q+q'):= by
    obtain ⟨x,hx⟩:= hp; obtain ⟨y',hy⟩:=hq; refine ⟨_,(hx.add hy).alter ?_⟩
    filter_upwards [wandering m u y h.works] with r hr; simp only [Pi.add_apply,stage,show fare c p (q+q') (D r) = fare c p q _ + fare c p q' _ from ((assay c hr 0 0) p).map_add q q',mul_add,Complex.ofReal_add]
  refine Submodule.span_induction (p:=fun v _=> W v q) ?_ (hy q).2 (fun a b _ _ h H=> he a b q h H) ?_ (hh p)
  · rintro v ⟨a,b,H,rfl⟩; refine Submodule.span_induction (p:=fun v _=> W (cell a b) v) ?_ (hy _).1 (fun a b _ _ h H=> hu _ a b h H) ?_ (hh q)
    · rintro v ⟨i,j,h,rfl⟩; exact hc a b i j
    rintro t v _ ⟨x,hx⟩; refine ⟨_,(hx.times (↑t:ℂ)).alter ?_⟩; filter_upwards [wandering m u y h.works] with r hr;
    simp only [stage,Pi.smul_apply,show fare c (cell a b) (t • v) (D r)=t*fare c (cell a b) v (D r) from map_smul (assay c hr 0 0 _) t _,Complex.ofReal_mul,smul_eq_mul]; ring
  rintro t z _ ⟨x,hx⟩; refine ⟨_,(hx.times (↑t:ℂ)).alter ?_⟩; filter_upwards [wandering m u y h.works] with r hr; simp only [stage,Pi.smul_apply,show fare c (t • z) q (D r)=t*fare c z q (D r) from LinearMap.congr_fun (map_smul (assay c hr 0 0) t z) q,Complex.ofReal_mul,smul_eq_mul]; ring

def residue (c:G.ColorIndex)(p q:Flavor 0) := (assuring h c p q).choose
lemma test_residue (c:G.ColorIndex)(p q: Flavor 0): Proves (stage c p q m u y) (residue h c p q):= (assuring h c p q).choose_spec
lemma normal_residue (c:G.ColorIndex) (a b i j:Axis): residue h c (cell a b) (cell i j)=spangle m u y a b i j:= by
  apply (test_residue ..).unique ((reflective h a b i j).alter ?_); filter_upwards [wandering m u y h.works] with r hr;
  unfold stage; rw [show fare c (cell a b) (cell i j) (D r)=bareCurl a b i j (D r) from ?_]
  have he:= raw_mixed (fun _:Fin 0=>0) (fun _:Fin 0=>0) a b i j c c hr; rw [if_pos rfl,pow_zero,one_mul, Tensor.coeff_apply_zero] at he; rw [Tensor.coeff_apply_zero] at he; exact he

def bilinear (c:G.ColorIndex) : Flavor 0 →ₗ[ℝ] Flavor 0→ₗ[ℝ] ℂ where
  toFun p:= {
    toFun q:= residue h c p q
    map_add' v w:= by
      refine (test_residue ..).unique (((test_residue h c p v).add (test_residue h c p w)).alter ?_); filter_upwards [wandering m u y h.works] with r hr
      simp only [stage, Pi.add_apply, show fare c p (v+w) _=fare c p v (D r)+fare c p w (D r) from ((assay c hr 0 0) p).map_add ..,mul_add,Complex.ofReal_add]
    map_smul' t q:= by
      change residue h c p (t • q)=(t:ℂ)*residue h c p q
      apply (test_residue ..).unique (((test_residue h c p q).times (t:ℂ)).alter ?_); filter_upwards [wandering m u y h.works] with r hr
      simp only [stage,Pi.smul_apply,show fare c p (t • q) (D r)=t*fare c p q (D r) from map_smul (assay c hr 0 0 p) t q]; push_cast; simp only [smul_eq_mul]; ring }
  map_add' p q:= by
    apply LinearMap.ext; intro x
    change residue h c (p+q) x=residue h c p x+residue h c q x
    apply (test_residue ..).unique (((test_residue h c p x).add (test_residue h c q x)).alter ?_); filter_upwards [wandering m u y h.works] with r hr
    simp only [stage, Pi.add_apply,show fare c (p+q) x (D r)=fare c p x (D r)+fare c q x (D r) from LinearMap.congr_fun ((assay c hr 0 0).map_add p q) x,mul_add, Complex.ofReal_add]
  map_smul' t p:= by
    apply LinearMap.ext; intro x
    change residue h c (t • p) x=(t:ℂ)*residue h c p x
    apply (test_residue ..).unique (((test_residue h c p x).times (t:ℂ)).alter ?_); filter_upwards [wandering m u y h.works] with r hr
    simp only [stage,Pi.smul_apply,show fare c (t • p) x (D r)=t*fare c p x (D r) from LinearMap.congr_fun (map_smul (assay c hr 0 0) t p) x]; push_cast; simp only [smul_eq_mul]; ring

lemma bill_lives (c:G.ColorIndex): bilinear h c≠0:= by
  intro H
  have ht (a b:Axis)(ha:a≠b): (d a)^2+(d b)^2=0:= by
    have he: residue h c (cell a b) (cell a b) =0:= DFunLike.congr_fun (DFunLike.congr_fun H _) _
    rw [normal_residue,spangle,mul_eq_zero] at he
    replace he:= he.resolve_left (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr normal_pos.ne')); simp only [kr_eq,ite_false,if_neg (Ne.symm ha),ha,ite_true, Complex.ofReal_zero,Complex.ofReal_one,one_mul,zero_mul,zero_sub,sub_zero] at he
    linear_combination -he
  have he i : d i=0:= by
    have hp:= ht 0 1 (by decide); have hx:= ht 1 2 (by decide); have hu:= ht 2 0 (by decide); have hl:= ht 0 3 (by decide)
    apply sq_eq_zero_iff.mp; fin_cases i
    · change d 0 ^ 2=0; linear_combination hp/2 - hx/2 + hu/2
    · change d 1 ^ 2=0; linear_combination hp/2 + hx/2 - hu/2
    · change d 2 ^ 2=0; linear_combination hx/2 + hu/2 - hp/2
    change d 3 ^ 2=0; linear_combination hl - (hp - hx + hu)/2
  apply h.works; ext1 i; simpa [corner] using congr_arg Complex.im (he i)
lemma partner (c:G.ColorIndex) (t:Sky m u x): ∃ v:Flavor 0, bilinear h c v ≠0 ∧ bilinear t c v≠0:= by
  let g : Bool→ Flavor 0 →ₗ[ℝ] Flavor 0→ₗ[ℝ] ℂ:=fun i=> if i then bilinear h c else bilinear t c
  haveI : Nontrivial (Flavor 0):=nontrivial_of_ne (cell 0 1) _ cell_alive -- cell_alive in Flavor
  obtain ⟨p,w,v⟩:= evade g Finset.univ; exact ⟨p,v true (Finset.mem_univ _) (bill_lives h c),v false (Finset.mem_univ _) (bill_lives t c)⟩
end YM.XSpace.ProbeLine
