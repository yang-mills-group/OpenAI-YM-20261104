import YM.XSpace.Equator

/-!
# Real bilinear color-scalar Laplacians preserve the whole span of tests

No symmetry of the formalism beyond these witnesses required, though our cases
will be symmetric by construction. Sign checks included, nilpotent exponential
understands *negative* covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal
open scoped BigOperators Topology Classical
variable {G : Gauge} (C₀:G.ColorIndex) {S:Finset E4} {L A : Finset (World G)} {h : ℕ} {P Q:Pol G}

abbrev Binary (S : Finset E4) (h : ℕ) := Supply S h →ₗ[ℝ] Module.Dual ℝ (Supply S h)
variable {K : Symmetric (World G)}

def Rich (K : Symmetric (World G)) (S : Finset E4) (h : ℕ) (A:Finset (World G)) :Prop:= ∃ B: Binary S h,
  ∀ i∈A,∀ j∈A,K.cov i j= if i.2.2=j.2.2 then (B (pronounce S h i) (pronounce S h j):ℂ) else 0
lemma Rich.neg (hp:Rich K S h A) : Rich (-K) S h A:=by
  obtain ⟨B,h⟩:=hp; refine ⟨-B,fun i hi j hj=>?_⟩; change -K.cov i j = _; rw [h i hi j hj]; split_ifs <;> simp

private lemma one_color_count (U W : Module.Dual ℝ (Supply S h)) (i j : World G):
    ∑ a:G.ColorIndex, backed U a i*backed W a j= if i.2.2=j.2.2 then ((U (pronounce S h i)*W (pronounce S h j):ℝ):ℂ) else (0:ℂ):=by
  rw [Finset.sum_eq_single_of_mem i.2.2 (Finset.mem_univ _) (fun b _ hb=> by rw [backed,if_neg (Ne.symm hb),zero_mul])]; by_cases hi:i.2.2=j.2.2 <;> simp_all [backed,Ne.symm]
private lemma tally (U W:Lane G) (hP:P ∈ Lap.scope A): plow U W P=∑ i∈A,∑ j∈A,(∑ a:G.ColorIndex, W a i * U a j) • slit (choose_var j 1) (slit (choose_var i 1) P):=by
  rw [plows]; have he (a) : slit (U a) (slit (W a) P)=∑ i∈A,∑ j∈A,(W a i*U a j) • slit (choose_var j 1) (slit (choose_var i 1) P):=by
    rw [split_sum _ A hP,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [(slit (U a)).map_smul,split_sum (U a) A (split_in _ _ hP),Finset.smul_sum]; simp_rw [smul_smul]
  simp_rw [he,Finset.sum_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
private lemma basis_lap {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (Supply S h)) (hP:P∈Lap.scope A)
    (B:Binary S h)
    (hB: ∀ i∈A,∀ j∈A,K.cov i j= if i.2.2=j.2.2 then (B (pronounce S h i) (pronounce S h j):ℂ) else 0):
    Lap.op A K P=∑ i:ι,plow (backed (B (b i))) (backed (b.coord i)) P:=by
  simp_rw [tally _ _ hP]; rw [Lap.op_at,Finset.sum_comm]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Finset.sum_comm,split_sum _ A (split_in _ _ hP)]
  apply Finset.sum_congr rfl; intro j hj; rw [← Finset.sum_smul,hB i hi j hj]; congr 1
  simp_rw [one_color_count]; split_ifs with hh
  · let u:=pronounce S h i; let v:=pronounce S h j
    rw [← Complex.ofReal_sum]; congr 1; change B u v= ∑ k, b.coord k u*B (b k) v
    conv_lhs=> rw [← b.sum_repr u,map_sum]
    rw [LinearMap.sum_apply]; simp_rw [_root_.map_smul,LinearMap.smul_apply,b.coord_apply]; rfl
  simp
include C₀ in
lemma rain_fields (V:Rich K S h A) (hA : Good S h A) (hP : P∈Rain S A): Lap.op A K P∈ Rain S A:=by
  obtain ⟨B,hB⟩:=V; rw [basis_lap (Module.Free.chooseBasis ℝ (Supply S h)) (rain_iff.mp hP).1 B hB]; exact Submodule.sum_mem _ fun i _=>every_plow C₀ hP hA ..
include C₀ in
lemma rain_milk (V:Rich K S h A) (hA : Good S h A) (hP : P∈Rain S A): milk K P∈ Rain S A:= Lap.stable _ K _ (fun _ h=>rain_fields C₀ V hA h) (rain_iff.mp hP).1 hP

-- The Cold Gaussian, on S, is exactly rich.
def two_voices (x y : E4) (j k:ℕ): Flavor j→ₗ[ℝ] Flavor k →ₗ[ℝ] ℝ := if he:x=y then 0 else assay C₀ (sub_ne_zero.mpr he) j k
def duplex (S : Finset E4) (h : ℕ): Binary S h where
  toFun u:= { toFun v:= ∑ x:(S:Set E4),∑ y:(S:Set E4),∑ j:Fin (h+1),∑ k:Fin (h+1), two_voices C₀ x y j k (u x j) (v y k)
              map_add' a b:= by simp [Finset.sum_add_distrib]
              map_smul' a b:= by simp [Finset.mul_sum] }
  map_add' a b:= by apply LinearMap.ext; intro v; simp [Finset.sum_add_distrib]
  map_smul' a b:= by apply LinearMap.ext; intro v; simp [Finset.mul_sum]
private lemma duplex_task (x y : (S:Set E4)) (j k : Fin (h+1)) (p : Flavor j) (q : Flavor k) :
    duplex C₀ S h (task h x j p) (task h y k q)=two_voices C₀ x y j k p q:=by
  unfold duplex; simp only [LinearMap.coe_mk, AddHom.coe_mk];
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (fun i _ hi => by simp [task,hi]), Finset.sum_eq_single_of_mem y (Finset.mem_univ _) (fun i _ hi=>by simp [task,hi])]
  simp only [task,Pi.single_eq_same]; rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun i _ hi=> by simp [hi]), Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hi=>by simp [hi]), Pi.single_eq_same,Pi.single_eq_same]
include C₀ in
lemma rich_cold (H:Good S h A): Rich (Cold S G) S h A:=by
  use duplex C₀ S h; intro i hi j hj; obtain ⟨e,p⟩:= H i hi; rw [cold_in e]; by_cases hr:i.1=j.1
  · obtain ⟨x,a⟩:=i; obtain ⟨y,b⟩:=j; obtain rfl:y=x:=hr.symm; rw [empty_self]; unfold pronounce; rw [dif_pos (H _ hi),dif_pos (H _ hj), duplex_task]; unfold two_voices; rw [dif_pos rfl]; simp
  rw [show (Kf G).cov i j=_ from colors C₀ hr i.2.1 j.2.1 i.2.2 j.2.2]; split_ifs with h
  · unfold pronounce; rw [dif_pos (H _ hi),dif_pos (H _ hj), duplex_task, two_voices, dif_neg (show i.1≠j.1 from hr)]; rfl
  rfl
include C₀ in
lemma rain_eval (H : Good S h A) (hP : P∈ Rain S A): aeval (0:World G→ℂ) P=0:=by
  have he:= (rain_iff.mp (rain_milk C₀ (rich_cold C₀ H).neg H hP)).2 ∅ 1 (Friends.baby S); let K:= Cold S G
  change Next.Rank.Normal.blend K 0 (1*_) = 0 at he; rw [one_mul,blend_components, Next.Rank.Normal.warms] at he; change aeval _ (milk (K + -K) P)=0 at he; rwa [K.cancels, froze] at he
end YM.XSpace.Legs
